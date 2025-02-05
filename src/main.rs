#![feature(closure_lifetime_binder)]
#![feature(box_vec_non_null)]

mod non_terminating_assoc_types;
mod sep_logic_permissions;
mod subtyping;

fn main() {
    subtyping::main();
    non_terminating_assoc_types::main();
}
