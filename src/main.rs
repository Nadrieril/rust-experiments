#![feature(closure_lifetime_binder)]
#![feature(box_vec_non_null)]

mod non_terminating_assoc_types;
mod sep_logic_in_types;
mod subtyping;

fn main() {
    if false {
        subtyping::main();
        non_terminating_assoc_types::main();
    }
    sep_logic_in_types::main();
}
