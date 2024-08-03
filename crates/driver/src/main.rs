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
use rustc_middle::util::Providers;
use rustc_session::Session;

struct MyCallbacks;

impl MyCallbacks {
    fn qoverride_queries(session: &Session, providers: &mut Providers) {
        /* FIXME if let Some(original) = original_queries.as_ref() {
            original(session, providers);
        }*/

        // Override specific query provider(s) here.
        /*        let original_typeck_tables_of = providers.typeck_tables_of;
        //std::mem::replace(&mut local_providers.typeck_tables_of, my_custom_typeck_tables_of);

        providers.typeck_tables_of = move |ctx, id| {
            // First, run regular type inference, i.e. the default Providers.typeck_tables_of(ctx, id).
            //let mut providers = rustc::ty::maps::Providers::default();
            //rustc_driver::driver::default_provide(&mut providers);
            let tables = original_typeck_tables_of(ctx, id);
            //let tables = (providers.typeck_tables_of)(ctx, id);
            let mut analyzer = dimanalysis::DimAnalyzer::new(ctx, tables, id);
            analyzer.analyze();
            tables
        };*/
    }
}

impl Callbacks for MyCallbacks {
    fn config(&mut self, config: &mut rustc_interface::Config) {
        let original_queries = config.override_queries.take();
        config.override_queries = Some(MyCallbacks::qoverride_queries);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    // Running the compiler with your custom callbacks.
    rustc_driver::RunCompiler::new(&args, &mut MyCallbacks)
        .run()
        .unwrap();
}
