//! Spent a night nerd-sniped about the code in https://rosettacode.org/wiki/Man_or_boy_test#Rust .
//! At first I wanted to understand it, so I slowly refactored and defunctionalized until I could
//! remove all interior mutability. Then I kept going, until I basically ended up computing a
//! closed form for that `a` function for each `k`.
use itertools::Itertools;
use std::collections::HashMap;

#[derive(Clone, Copy)]
struct Factor {
    coeff: i32,
    var_id: usize,
}

impl std::fmt::Display for Factor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.coeff == 1 {
            write!(f, "v{}", self.var_id)
        } else {
            write!(f, "{} * v{}", self.coeff, self.var_id)
        }
    }
}
impl std::fmt::Debug for Factor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl Factor {
    fn var(var_id: usize) -> Self {
        Self { coeff: 1, var_id }
    }
    fn decr_var(self) -> Self {
        Self {
            coeff: self.coeff,
            var_id: self.var_id - 1,
        }
    }
}

fn run_params(target_k: i32) -> (i32, &'static [Factor]) {
    // Store for each `k` a delta to apply to that `k` and the array indices to sum. Note that we
    // store the entry for `k` at index `k + 1`.
    let mut data_for_k: Vec<(i32, Box<[Factor]>)> =
        vec![(-1, Box::new([Factor::var(3), Factor::var(4)]))];

    for mut k in 0..target_k {
        // Base array, where `0` refers to a whole previous node.
        let base: &[_] = match k {
            ..=0 => &[Factor::var(3), Factor::var(4)],
            1 => &[Factor::var(2), Factor::var(3)],
            2 => &[Factor::var(1), Factor::var(2)],
            3 => &[Factor::var(0), Factor::var(1)],
            4.. => {
                let (_, array) = &data_for_k[k as usize];
                let array: Box<[_]> = array.iter().map(|f| f.decr_var()).collect();
                Box::leak(array)
            }
        };

        // Replace the factors with index `0`.
        let mut total_delta = 0;
        let mut coeff_per_var: HashMap<usize, i32> = HashMap::new();
        for &f in base {
            if f.var_id == 0 {
                let mut iter = 0..f.coeff;
                while let Some(_) = iter.next() {
                    // If `k < 0`, we know all subsequent iterations will hit the `0` case and
                    // result in the same values. In that case we short-circuit by consuming the
                    // rest of the iterator and multiplying the values accordingly.
                    let coeff = 1 + if k < 0 {
                        iter.by_ref().count() as i32
                    } else {
                        0
                    };
                    let (delta, new_array) = &data_for_k[if k < 0 { 0 } else { k as usize }];
                    k += delta * coeff;
                    total_delta += delta * coeff;
                    for g in new_array {
                        *coeff_per_var.entry(g.var_id).or_default() += g.coeff * coeff;
                    }
                }
            } else {
                *coeff_per_var.entry(f.var_id).or_default() += f.coeff;
            }
        }

        let array = coeff_per_var
            .into_iter()
            .sorted()
            .map(|(var_id, coeff)| Factor { coeff, var_id })
            .collect();
        data_for_k.push((total_delta - 1, array));
    }

    let (delta, array) = &data_for_k[if target_k < 0 { 0 } else { target_k as usize }];
    (target_k + delta, Box::leak(array.clone()))
}

fn sum_up(xs: &[i32], ns: &[Factor]) -> i32 {
    ns.iter().map(|f| f.coeff * xs[f.var_id - 1]).sum()
}

pub fn main() {
    for k in 0..=25 {
        let (new_k, array) = run_params(k);
        println!("{k}: {new_k}, {array:?}");
    }

    let (new_k, array) = run_params(10);
    let n = sum_up(&[1, -1, -1, 1], array);
    assert_eq!(new_k, -53);
    assert_eq!(n, -67);
}
