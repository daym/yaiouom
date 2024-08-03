use rustc_hir as hir;
use rustc_hir::def_id::DefId;
use rustc_hir::intravisit::{self, Visitor};
use rustc_middle::ty;
use rustc_middle::ty::{Ty, TyCtxt, TypeckResults};

//use rustc_ast::ast;
//use rustc_attr as attr;
use rustc_span::Span;
use rustc_span::Symbol;

use std;
use std::collections::{HashMap, HashSet};

const YAOIOUM_ATTR_CHECK_UNIFY: &str = "rustc_yaiouom_check_unify";
const YAOIOUM_ATTR_COMBINATOR_MUL: &str = "rustc_yaiouom_combinator_mul";
const YAOIOUM_ATTR_COMBINATOR_INV: &str = "rustc_yaiouom_combinator_inv";
const YAOIOUM_ATTR_COMBINATOR_DIMENSIONLESS: &str = "rustc_yaiouom_combinator_dimensionless";

/// If this def-id is a "primary tables entry", returns `Some((body_id, decl))`
/// with information about it's body-id and fn-decl (if any). Otherwise,
/// returns `None`.
///
/// If this function returns "some", then `typeck_tables(def_id)` will
/// succeed; if it returns `None`, then `typeck_tables(def_id)` may or
/// may not succeed.  In some cases where this function returns `None`
/// (notably closures), `typeck_tables(def_id)` would wind up
/// redirecting to the owning function.
fn primary_body_of<'a, 'tcx>(
    _tcx: TyCtxt<'tcx>, // 'a
    node: hir::Node<'a>,
) -> Option<(hir::BodyId, Option<&'tcx hir::FnDecl<'a>>)> {
    match node {
        hir::Node::Item(item) => match item.kind {
            hir::ItemKind::Const(_, _, body) | hir::ItemKind::Static(_, _, body) => {
                Some((body, None))
            }
            hir::ItemKind::Fn(ref sig, .., body) => Some((body, Some(sig.decl))),
            _ => None,
        },
        hir::Node::TraitItem(item) => match item.kind {
            hir::TraitItemKind::Const(_, Some(body)) => Some((body, None)),
            hir::TraitItemKind::Fn(ref sig, hir::TraitFn::Provided(body)) => {
                Some((body, Some(sig.decl)))
            }
            _ => None,
        },
        hir::Node::ImplItem(item) => match item.kind {
            hir::ImplItemKind::Const(_, body) => Some((body, None)),
            hir::ImplItemKind::Fn(ref sig, body) => Some((body, Some(sig.decl))),
            _ => None,
        },
        hir::Node::Expr(expr) => {
            // FIXME(eddyb) Closures should have separate
            // function definition IDs and expression IDs.
            // Type-checking should not let closures get
            // this far in a constant position.
            // Assume that everything other than closures
            // is a constant "initializer" expression.
            match expr.kind {
                hir::ExprKind::Closure(..) => None,
                _ => Some((
                    hir::BodyId {
                        hir_id: expr.hir_id,
                    },
                    None,
                )),
            }
        }
        _ => None,
    }
}

struct UnitConstraints<'tcx> {
    tcx: TyCtxt<'tcx>,
    left: HashMap<Ty<'tcx>, (HashSet<Span>, i32)>,
    right: HashMap<Ty<'tcx>, (HashSet<Span>, i32)>,
    def_id: DefId,
    span: Span,
}
impl<'tcx> std::fmt::Debug for UnitConstraints<'tcx> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> std::result::Result<(), std::fmt::Error> {
        write!(formatter, "{:?}/{:?}", self.left, self.right)
    }
}
impl<'tcx> UnitConstraints<'tcx> {
    fn describe(&self, left: bool) -> String {
        let mut buf = String::new();
        let mut first = true;
        let table = if left { &self.left } else { &self.right };
        for (ty, (_, ref number)) in table {
            let name = match ty.kind() {
                ty::Adt(ref def, _) => self.tcx.def_path(def.did()).to_string_no_crate_verbose(),
                ty::Param(ref param) => {
                    // TyParam
                    let generics = self.tcx.generics_of(self.def_id);
                    let def = generics.type_param(*param, self.tcx);
                    self.tcx.def_path(def.def_id).to_string_no_crate_verbose() // def.def_id
                }
                _ => unimplemented!(),
            };
            let exp = if *number == 1 {
                "".to_string()
            } else {
                format!("^{}", number)
            };
            buf.push_str(&format!(
                "{mul}{name}{exp}",
                mul = if first { "" } else { " * " },
                name = name,
                exp = exp
            ));
            if first {
                first = false;
            }
        }
        buf
    }
}

impl<'tcx> UnitConstraints<'tcx> {
    fn from(tcx: TyCtxt<'tcx>, span: Span, def_id: DefId) -> Self {
        // 'v
        Self {
            tcx,
            def_id,
            left: HashMap::new(),
            right: HashMap::new(),
            span,
        }
    }
    fn add_one(&mut self, ty: Ty<'tcx>, span: Span, left: bool, positive: bool) {
        let table = if left {
            &mut self.left
        } else {
            &mut self.right
        };
        let known = table.entry(ty).or_insert_with(|| (HashSet::new(), 0));
        known.0.insert(span);
        if positive {
            known.1 += 1;
        } else {
            known.1 -= 1;
        }
    }

    /// Add a type involved in a unit-of-measure level unification.
    fn add(&mut self, ty: Ty<'tcx>, left: bool, positive: bool) -> Result<(), ()> {
        match ty.kind() {
            ty::Adt(def, subst) => {
                // A constructor `Foo<A, B, C...>`.
                //
                // Since we are in a unit-of-measure unification, `Foo` could be
                // `Mul`, `Inv`, `Dimensionless` (in which case they are handled
                // as operators) or any other type (in which case they are handled
                // as base units).
                let span = self.tcx.def_span(def.did());
                if self
                    .tcx
                    .has_attr(def.did(), Symbol::intern(YAOIOUM_ATTR_COMBINATOR_MUL))
                {
                    for item in subst.types() {
                        self.add(item, left, positive)?;
                    }
                } else if self
                    .tcx
                    .has_attr(def.did(), Symbol::intern(YAOIOUM_ATTR_COMBINATOR_INV))
                {
                    for item in subst.types() {
                        self.add(item, left, !positive)?;
                    }
                } else if self.tcx.has_attr(
                    def.did(),
                    Symbol::intern(YAOIOUM_ATTR_COMBINATOR_DIMENSIONLESS),
                ) {
                    // Nothing to do.
                } else {
                    self.add_one(ty, span, left, positive);
                }
                Ok(())
            }
            ty::Param(param) => {
                let generics = self.tcx.generics_of(self.def_id);
                let def = generics.type_param(*param, self.tcx);
                let span = self.tcx.def_span(def.def_id);
                self.add_one(ty, span, left, positive);
                Ok(())
            }
            /*
                ty::Error => {
                    // There's already a type error, skipping.
                    Err(())
            }
                */
            _ => panic!("I shouldn't have received ty {:?}", ty),
        }
    }

    /// Remove everything that has multiplicity 0.
    fn simplify(&mut self) {
        self.left.retain(|_, v| v.1 != 0);
        self.right.retain(|_, v| v.1 != 0);
    }
}

struct GatherConstraintsVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    tables: &'tcx TypeckResults<'tcx>,
    constraints: Vec<UnitConstraints<'tcx>>,
    def_id: DefId,
}
impl<'tcx> GatherConstraintsVisitor<'tcx> {
    fn add_unification(&mut self, left: Ty<'tcx>, right: Ty<'tcx>, span: Span) {
        // eprintln!("dim_analyzer: We need to unify {:?} == {:?}", left, right);

        let mut constraint = UnitConstraints::from(self.tcx, span, self.def_id);
        if constraint.add(left, true, true).is_err() {
            // Don't pile up constraints on top of existing errors.
            return;
        }
        if constraint.add(right, false, true).is_err() {
            // Don't pile up constraints on top of existing errors.
            return;
        }
        constraint.simplify();
        if constraint.left != constraint.right {
            self.constraints.push(constraint)
        }
    }
}

impl<'v, 'tcx> Visitor<'v> for GatherConstraintsVisitor<'tcx> {
    fn visit_expr(&mut self, expr: &'v hir::Expr) {
        if let hir::ExprKind::MethodCall(segment, _, args, _) = expr.kind {
            // Main interesting case: a call to `some_expr.unify()`
            let (_def_kind, def_id) = self.tables.type_dependent_defs()[expr.hir_id].unwrap();
            /*            let def_id = self
            .tcx
            .typeck_body(tcx.hir().get_if_local(self.def_id)
            .type_dependent_def_id(expr.hir_id)
            .unwrap();*/
            //caller_def_id.to_def_id()
            if self
                .tcx
                .has_attr(def_id, Symbol::intern(YAOIOUM_ATTR_CHECK_UNIFY))
            {
                // if self.tcx.has_attr(caller_def_id.to_def_id(), sym::your_attr_name) {
                // This is a call to `unify`.
                let substs = self.tables.node_args(expr.hir_id); // FIXME test

                // By definition, `unify` has type `<V: Unit>(self: Measure<T, U>) -> Measure<T, V>`.
                // Extract `U` and `V`. We don't care about `T`, it has already been checked
                // by type inference.
                self.add_unification(substs.type_at(1), substs.type_at(2), expr.span);
            }

            // Debug note: You can println! here if you want to see what's being processed during compilation
            //println!("{:?}, {:?}, {:?}", segment, args, caller_def_id);
        }

        // Proceed with walking down the expression tree
        intravisit::walk_expr(self, expr);
    }
}

pub struct DimAnalyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
    tables: &'tcx TypeckResults<'tcx>,
    def_id: DefId,
}

impl<'tcx> DimAnalyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, tables: &'tcx TypeckResults<'tcx>, def_id: DefId) -> Self {
        Self {
            tcx,
            tables,
            def_id,
        }
    }

    pub fn analyze(&mut self) {
        // eprintln!("\n\n\ndim_analyzer: -----------   analyze {:?}", self.def_id);
        if self.tables.tainted_by_errors.is_some() {
            // eprintln!("dim_analyzer: Don't proceed with analysis, there is already an error");
            return;
        }

        // Closures' tables come from their outermost function,
        // as they are part of the same "inference environment".
        // FIXME let outer_def_id = self.tcx.closure_base_def_id(self.def_id);
        // FIXME if outer_def_id != self.def_id {
        // FIXME    return;
        // FIXME }

        let node = self.tcx.hir().get_if_local(self.def_id).unwrap();
        let span = self.tcx.hir().span_if_local(self.def_id).unwrap();

        // Figure out what primary body this item has.
        let (body_id, fn_decl) = primary_body_of(self.tcx, node).unwrap_or_else(|| {
            panic!(
                "{:?}: dim_analyzer can't type-check body of {:?}",
                span, self.def_id
            );
        });
        let body = self.tcx.hir().body(body_id);
        // eprintln!("dim_analyzer: body {:?}", body);

        if fn_decl.is_some() {
            // eprintln!("dim_analyzer: This is a function declaration");
            let mut visitor = GatherConstraintsVisitor {
                tcx: self.tcx,
                tables: self.tables,
                constraints: vec![],
                def_id: self.def_id,
            };
            visitor.visit_body(body);
            if !visitor.constraints.is_empty() {
                use rustc_errors::DiagStyledString;
                for constraint in visitor.constraints.drain(..) {
                    // FIXME rustc_errors::struct_span_code_err(dcx, span, code, ...)
                    let mut builder = self.tcx.dcx().struct_span_err(
                        constraint.span,
                        "Cannot resolve the following units of measures:",
                    );
                    let mut expected = DiagStyledString::new();
                    expected.push_normal(constraint.describe(true));

                    let mut found = DiagStyledString::new();
                    found.push_normal(constraint.describe(false));

                    builder.note_expected_found(&"unit of measure:", expected, &"found", found);
                    builder.span_label(constraint.span, "in this unification");
                    builder.span_label(span, "While examining this function");
                    builder.emit();
                }
            }
        }
    }
}
