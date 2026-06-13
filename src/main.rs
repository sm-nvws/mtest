use spartan_rs::arena::with_scope;
use spartan_rs::axioms::build_analysis;
use spartan_rs::check::{check, reset_levels, solve_levels};
use spartan_rs::context::Context;
use spartan_rs::env::Env;
use spartan_rs::norm::eval;
use spartan_rs::signature::Signature;

fn main() {
    reset_levels();
    with_scope(|arena| {
        let mut sig = Signature::new();
        let ctx = Context::new();
        let env = Env::new();

        let analysis = build_analysis(&arena, &mut sig);

        let steps = [
            (
                "Cauchy criterion (from completeness)",
                analysis.cauchy_proof,
                analysis.cauchy_thm,
            ),
            (
                "Uniform convergence from Cauchy + majorization",
                analysis.uniform_proof,
                analysis.mtest_stmt,
            ),
            (
                "Weierstrass M-test",
                analysis.mtest_proof,
                analysis.mtest_stmt,
            ),
        ];

        for (label, proof, stmt) in steps {
            let stmt_val = eval(&arena, &sig, stmt, &env);
            if let Err(e) = check(&arena, &sig, &ctx, &env, proof, stmt_val) {
                eprintln!("{label} failed:\n{:?}", miette::Report::new(e));
                std::process::exit(1);
            }
        }

        if let Err(e) = solve_levels() {
            eprintln!("level solve failed: {e:?}");
            std::process::exit(1);
        }

        println!("proof accepted.");
    });
}
