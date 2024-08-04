#![feature(rustc_private)]

//extern crate getopts;

//extern crate rustc;
extern crate rustc_ast;
extern crate rustc_attr;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod dimanalysis;

//use rustc_interface::interface::Compiler;
use rustc_driver::Callbacks;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty;
use rustc_middle::ty::{Ty, TyCtxt, TypeckResults};
use rustc_middle::util::Providers;
use rustc_session::Session;
struct MyCallbacks;

impl MyCallbacks {
    fn typeck(ctxt: TyCtxt, def_id: LocalDefId) -> &ty::TypeckResults {
        let providers = Providers::default();
        //rustc_driver::default_provide(&mut providers);
        let result = (providers.typeck)(ctxt, def_id).to_owned();
        let mut analyzer = dimanalysis::DimAnalyzer::new(ctxt, result, def_id.into());
        analyzer.analyze();
        result
    }
    fn diagnostic_only_typeck(ctxt: TyCtxt, def_id: LocalDefId) -> &ty::TypeckResults {
        let providers = Providers::default();
        //rustc_driver::default_provide(&mut providers);
        let result = (providers.diagnostic_only_typeck)(ctxt, def_id).to_owned();
        let mut analyzer = dimanalysis::DimAnalyzer::new(ctxt, result, def_id.into());
        analyzer.analyze();
        result
    }
    fn override_queries(session: &Session, providers: &mut Providers) {
        providers.typeck = Self::typeck;
        providers.diagnostic_only_typeck = Self::diagnostic_only_typeck;
    }
}

impl Callbacks for MyCallbacks {
    fn config(&mut self, config: &mut rustc_interface::Config) {
        config.override_queries = Some(Self::override_queries);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    // Running the compiler with your custom callbacks.
    rustc_driver::RunCompiler::new(&args, &mut MyCallbacks)
        .run()
        .unwrap();
}
