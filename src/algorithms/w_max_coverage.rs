#![allow(unused_imports, dead_code)]

use good_lp::variable::UnsolvedProblem;
use good_lp::{
    constraint, default_solver, variable, variables, Expression, IntoAffineExpression, Solution,
    SolverModel,
};
use std::collections::HashSet;
use std::iter::Sum;
use std::ops::Mul;

use crate::Attestation;

/// A problem instance for the Weighted Maximum Coverage problem with sets `sets`, element weights
/// `weights`, and maximum limit `k`.
pub struct WeightedMaximumCoverage {
    /// Sets to select from
    pub sets: Vec<Vec<usize>>,
    /// Weights of the elements
    pub weights: Vec<f64>,
    /// Limit for the size of the solution (number of selected sets)
    pub k: usize,
}

#[allow(unused_variables)]
impl WeightedMaximumCoverage {
    /// Solves the Weighted Maximum Coverage using a MIP solver.
    pub fn solve(&self) -> Result<Vec<usize>, &str> {
        // produce lists of sets containing a given element
        let mut sets_with: Vec<Vec<usize>> = vec![];
        sets_with.resize_with(self.weights.len(), Vec::new);
        for i in 0..self.sets.len() {
            for &j in &self.sets[i] {
                sets_with[j].push(i);
            }
        }

        let mut vars = variables!();

        // initialise set variables
        let xs = vars.add_vector(variable().binary(), self.sets.len());

        // initialise element variables
        let ys = vars.add_vector(variable().min(0.0).max(1.0), self.weights.len());

        // define objective function as linear combination of element variables and weights
        let objective =
            Expression::sum((0..self.weights.len()).map(|yi| ys[yi].mul(self.weights[yi])));
        let mut problem = vars.maximise(objective).using(default_solver);

        // limit solution size to k sets
        problem = problem.with(Expression::sum(xs.iter()).leq(self.k as f64));

        // add constraint allowing to cover an element only if one of the sets containing it is included
        for j in 0..self.weights.len() {
            problem = problem.with(constraint! {
                Expression::sum(sets_with[j].iter().map(|i| xs[*i])) >= ys[j]
            });
        }

        // tell CBC not to log
        problem.set_parameter("log", "0");

        // should be safe to `unwrap` since the problem is underconstrained
        let solution = problem.solve().unwrap();

        // report solution
        let mut coverage = Vec::with_capacity(self.weights.len());
        xs.iter()
            .enumerate()
            .filter(|(_, &x)| solution.value(x) > 0.0)
            .for_each(|(i, _)| coverage.push(i));

        Ok(coverage)
    }

    pub fn greedy_solution(&mut self) -> Result<Vec<usize>, &str> {
        let mut res = vec![];

        for num in 0..(self.k) {
            let score_vec: Vec<f64> = self
                .sets
                .iter()
                .map(|attesters| {
                    attesters
                        .iter()
                        .map(|attester| self.weights[*attester])
                        .sum()
                })
                .collect();

            let max_index = score_vec
                .iter()
                .enumerate()
                .filter(|&(_, &value)| value.is_finite()) // filter out NaN values
                .max_by(|&(_, a), &(_, b)| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
                .map(|(index, _)| index)
                .unwrap();

            res.push(max_index);
            let attesters_to_cull: HashSet<usize> =
                self.sets[max_index].clone().into_iter().collect();
            self.sets.iter_mut().for_each(|attester_set| {
                let mut indices_to_remove = vec![];
                for (index, attester) in attester_set.iter().enumerate() {
                    if attesters_to_cull.contains(attester) {
                        indices_to_remove.push(index);
                    }
                }
                for index in indices_to_remove.iter().rev() {
                    attester_set.remove(*index);
                }
            });
        }
        Ok(res)
    }

    // pub fn enum_solve(&self) -> Vec<Vec<usize>> {
    //     let mut b: Vec<Vec<usize>> = vec![];
    //     let r = &self.sets;
    //     enum_solve_aux(vec![], HashSet::new(), r, &mut b, self.k, 0, &self.weights);
    // }
}

// // w: The current working solution to the WeightedMaximumCoverage problem
// // r: The remaining attestations to be considered for the solution
// // b: The best solution seen so far
// // k: the maximum number of attestations that can be used
// // i: the current index to consider as the beginning of the remaining attestations set
// pub fn enum_solve_aux(
//     w: Vec<Vec<usize>>,
//     w_set: HashSet<usize>,
//     r: &Vec<Vec<usize>>,
//     b: &mut Vec<Vec<usize>>,
//     k: usize,
//     i: usize,
//     weights: &Vec<f64>,
// ) {
//     if i < r.len() && w.len() < k {
//         for attestation in r {
//             let mut c = w.clone();
//             c.push(attestation.clone());
//             let mut c_set = w_set.clone();
//             c_set.extend(attestation);
//             if rewards(&mut c, weights) > rewards(b, weights) {
//                 *b = c.clone();
//             }
//             let r_prime: Vec<Vec<usize>> = r.clone().into_iter().filter(|r_att| {
//                 r_att.iter()
//                     .cloned()
//                     .collect::<HashSet<usize>>()
//                     .intersection(&c_set)
//                     .next()
//                     .is_some()
//             }).collect();
//             let mut p: Vec<f64> = r_prime.iter().map(|r| rewards(&vec![r.clone()], weights)).collect();
//             p.sort_by(|a, b| b.partial_cmp(a).unwrap());
//             let p_val: f64 = p.iter().take(k - c.len()).sum();
//             if rewards(&c, weights) + p_val > rewards(b, weights) {
//                 enum_solve_aux(c, c_set, &r_prime, b, k, i, weights)
//             }
//         }
//     }
// }

// // w: The current working solution to the WeightedMaximumCoverage problem (indices of sets)
// // r: The remaining attestations to be considered for the solution
// // b: The best solution seen so far
// // k: the maximum number of attestations that can be used
// // i: the current index to consider as the beginning of the remaining attestations set
// pub fn enum_solve_aux2(
//     w: Vec<usize>,
//     w_set: HashSet<usize>,
//     r: Vec<usize>,
//     b: &mut Vec<Vec<usize>>,
//     k: usize,
//     i: usize,
//     weights: &Vec<f64>,
//     sets: &Vec<Vec<usize>>,
// ) {
//     if r.len() > 0 && w.len() < k {
//         for attestation in r {
//             let mut c = w.clone();
//             c.push(attestation.clone());
//             let mut c_set = w_set.clone();
//             c_set.extend(attestation);
//             if rewards(&mut c, weights) > rewards(b, weights) {
//                 *b = c.clone();
//             }
//             let r_prime: Vec<Vec<usize>> = r.clone().into_iter().filter(|r_att| {
//                 r_att.iter()
//                     .cloned()
//                     .collect::<HashSet<usize>>()
//                     .intersection(&c_set)
//                     .next()
//                     .is_some()
//             }).collect();
//             let mut p: Vec<f64> = r_prime.iter().map(|r| rewards(&vec![r.clone()], weights)).collect();
//             p.sort_by(|a, b| b.partial_cmp(a).unwrap());
//             let p_val: f64 = p.iter().take(k - c.len()).sum();
//             if rewards(&c, weights) + p_val > rewards(b, weights) {
//                 enum_solve_aux(c, c_set, &r_prime, b, k, i, weights)
//             }
//         }
//     }
// }

pub fn rewards(included_attestations: &Vec<Vec<usize>>, weights: &Vec<f64>) -> f64 {
    let mut unique_attesters: HashSet<usize> = HashSet::new();
    for attestation in included_attestations {
        for attester in attestation {
            unique_attesters.insert(*attester);
        }
    }

    unique_attesters
        .iter()
        .map(|attester| weights[*attester])
        .sum()
}

mod tests {
    use crate::algorithms::w_max_coverage::WeightedMaximumCoverage;

    #[test]
    fn small_coverage() {
        let p = WeightedMaximumCoverage {
            sets: vec![
                vec![0, 1, 2],
                vec![0, 3],
                vec![1, 2],
                vec![3, 2],
                vec![0, 4],
                vec![2, 3, 0],
            ],
            weights: vec![12.1, 11.3, 3.9, 2.3, 8.2],
            k: 2,
        };

        println!("{:?}", p.solve());
    }
}
