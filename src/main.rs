#![feature(closure_lifetime_binder)]
mod non_terminating_assoc_types;
mod sep_logic_permissions;
mod subtyping;

fn main() {
    subtyping::main();
    non_terminating_assoc_types::main();
}
