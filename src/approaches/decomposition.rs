use crate::aapp::instance::{Attestation, AttestationData, EpochAttesterID, Instance};
use crate::algorithms::{bron_kerbosh, WeightedMaximumCoverage};
use std::collections::{HashMap, HashSet};
use std::time::Instant;
use itertools::Itertools;

pub fn decomposition_approach(instance: &Instance) {
    let start = Instant::now();

    // group attestations by data
    let aggregated_atts = group_by_att_data(&instance.aggregated_attestations);
    let unaggregated_atts = group_by_att_data(&instance.unaggregated_attestations);

    let mut num_cliques = vec![];

    let mut data_vec: Vec<&AttestationData> = vec![];
    let mut cliqued_atts: Vec<Vec<Vec<EpochAttesterID>>> = vec![];

    let mut total_attestations = 0;
    for (data, attestations) in &aggregated_atts {
        total_attestations += attestations.len();
        // derive cliques for current attestation data
        let cliques = bron_kerbosh(attestations, is_compatible);
        let mut cliques: Vec<Vec<EpochAttesterID>> = cliques
            .iter()
            .map(|clique| {
                clique
                    .iter()
                    .flat_map(|att_idx| &attestations[*att_idx].attesting_indices)
                    .cloned()
                    .collect()
            })
            .collect();

        // extract attester sets
        let attesters: Vec<EpochAttesterID> = unaggregated_atts
            .get(data)
            .cloned()
            .or_else(|| Some(vec![]))
            .unwrap()
            .iter()
            .map(|attestation| attestation.attesting_indices[0])
            .collect();

        for attester in &attesters {
            for clique in &mut cliques {
                if !clique.contains(attester) {
                    clique.push(*attester)
                }
            }
        }

        // add aggregated attestation based on all unaggregated attestations (U)
        // cliques.push(attesters);
        data_vec.push(data);
        cliqued_atts.push(cliques.clone());
        num_cliques.push(cliques.len());
    }

    for (data, attestations) in &unaggregated_atts {
        total_attestations += unaggregated_atts.len();
        if !aggregated_atts.contains_key(data) {
            let attesters: Vec<EpochAttesterID> = attestations
                .iter()
                .map(|attestation| attestation.attesting_indices[0])
                .collect();

            cliqued_atts.push(vec![attesters]);
            data_vec.push(data);
        }
        num_cliques.push(1);
    }

    // R(f(0,m)) = 0 => val_map[0][0] = 0
    // R(f(1,0)) => val_map[1][0] 
    // ...
    //
    // each vector inside the val_map has length q_i = min(m, clique.len())
    // val_map[i] := the ith datas computed values in order from 0 -> q_i
    let mut val_map: Vec<Vec<f64>> = vec![vec![]; cliqued_atts.len()];
    let mut max_val_ind: Vec<usize> = vec![]; 

    let mut attesters_map: Vec<Vec<Vec<Vec<EpochAttesterID>>>> = vec![vec![]; cliqued_atts.len()];
    // iterate over vectors of vectors of cliques 
    // index: usize
    // clique_set: Vec<Vec<EpochAttesterID>>
    // one clique is a Vec<EpochAttesterID>
    for (index, clique_set) in cliqued_atts.iter().enumerate() {
        let new_to_old: Vec<EpochAttesterID> = clique_set
            .iter()
            .flatten()
            .unique()
            .cloned()
            .collect();

        let old_to_new: HashMap<EpochAttesterID, usize> = new_to_old
            .iter()
            .enumerate()
            .map(|(idx, attester)| (*attester, idx))
            .collect();

        let reindexed_atts: Vec<Vec<usize>> = clique_set
            .iter()
            .map(|clique| clique.iter().map(|attester| old_to_new[attester]).collect())
            .collect();

        let reindexed_weights: Vec<f64> = new_to_old
            .iter()
            .map(|attester| instance.reward_function.get(attester))
            .map(|weight| weight.copied().unwrap_or(0) as f64)
            .collect();
        
        let max_domain = std::cmp::min(128, clique_set.len()); 
        let mut max_ind_over_domain = 0;
        let mut max_val = 0.0;

        for i in 0..=max_domain {
            let second_ind = if index == 0 {
                0
            } else {
                if 128 - i < val_map[index - 1].len() {
                    128 - i
                } else {
                    val_map[index - 1].len() - 1
                }
            };

            let f_val = if index == 0 {
                0.0
            } else {
                // there might be an off by 1 error here
                val_map[index - 1][second_ind]
            };

            let f_attestations: Vec<Vec<EpochAttesterID>> = if index > 0 {
                attesters_map[index - 1][second_ind].clone()
            } else {
                vec![]
            };

            let g_vec: Vec<usize> = if i == 0 {
                vec![]
            } else {
                let wmcp = WeightedMaximumCoverage {
                    sets: reindexed_atts.clone(),
                    weights: reindexed_weights.clone(),
                    k: i,
                };

                // let mip_start = Instant::now();
                wmcp.solve().unwrap()
            }; 

            let mut final_attesters: Vec<Vec<EpochAttesterID>> =
                g_vec.iter().map(|idx| clique_set[*idx].clone()).collect();

            let g_val = calculate_reward(&final_attesters, &instance.reward_function);
            val_map[index].push(f_val + g_val);
            final_attesters.extend(f_attestations);

            attesters_map[index].push(final_attesters);

            if f_val + g_val > max_val {
                max_val = f_val + g_val;
                max_ind_over_domain = i;
            }
        }
        max_val_ind.push(max_ind_over_domain);
    }

    let optimal_second_ind = *max_val_ind.last().unwrap();
    let optimal_reward = val_map.last().unwrap()[optimal_second_ind];
    let final_attesters = &attesters_map.last().unwrap()[optimal_second_ind];
    println!("final_attesters: {}", final_attesters.len());
    println!("last val_map: {:?}", val_map.last().unwrap());
    // println!("val_map: {:?}", val_map);
    println!("num_cliques: {}", num_cliques.iter().sum::<usize>());
    println!("total attestations: {}", total_attestations);

    print!("{}", instance.slot.0);

    print!(
        ",{},{}",
        &final_attesters
            .iter()
            .flatten()
            .collect::<HashSet<_>>()
            .len(),
        optimal_reward
    );
    let greedy_reward = calculate_reward(&instance.greedy_solution, &instance.reward_function);
    print!(
        ",{},{},{:.5}",
        &instance
            .greedy_solution
            .iter()
            .flatten()
            .collect::<HashSet<_>>()
            .len(),
        greedy_reward,
        1.0 - (greedy_reward / optimal_reward)
    );

    let end = Instant::now();

    print!(
        ",{}",
        end.duration_since(start).as_millis()      // all duration
    );

    print!(
        ", min cliques {}, max cliques {}, average cliques {:.5}",
        num_cliques.iter().min().unwrap(),
        num_cliques.iter().max().unwrap(),
        num_cliques.iter().map(|&x| x as f64).sum::<f64>() / (num_cliques.len() as f64),
    );

    let unique_agg: HashSet<AttestationData> = instance
        .aggregated_attestations
        .iter()
        .map(|att| att.data_root)
        .collect();
    let unique_unagg: HashSet<AttestationData> = instance
        .unaggregated_attestations
        .iter()
        .map(|att| att.data_root)
        .collect();
    let n_unique = unique_agg
        .union(&unique_unagg)
        .collect::<HashSet<&AttestationData>>()
        .len();

    println!(",{}", n_unique) // number of unique attestation data
}

fn group_by_att_data(
    attestations: &Vec<Attestation>,
) -> HashMap<AttestationData, Vec<Attestation>> {
    let mut ret: HashMap<AttestationData, Vec<Attestation>> = HashMap::new();
    for attestation in attestations {
        ret.entry(attestation.data_root)
            .or_default()
            .push(attestation.clone());
    }
    ret
}

fn is_compatible(x: &Attestation, y: &Attestation) -> bool {
    let x_attester_set: HashSet<_> = x.attesting_indices.iter().collect();
    let y_attester_set: HashSet<_> = y.attesting_indices.iter().collect();
    x_attester_set.is_disjoint(&y_attester_set)
}

fn calculate_reward(
    attesters: &[Vec<EpochAttesterID>],
    weights: &HashMap<EpochAttesterID, u64>,
) -> f64 {
    let unique_attesters = attesters.iter().flatten().collect::<HashSet<_>>();

    unique_attesters
        .iter()
        .map(|attester| weights.get(attester).unwrap_or(&0))
        .map(|weight| *weight as f64)
        .sum()
}

fn calculate_f_from_map(
    f_map: Vec<Vec<f64>>,
    capacity: usize,
    k: usize,
    m: usize,
    q: usize,
) -> f64 { 
    let answer = if k == 0 || m == 0 {
        0.0
    } else {
        f_map[k-1][m-q]  
    };
    answer
}

#[allow(unused_imports)]
mod tests {
    use super::*;
    use crate::{Instance, RawInstance};

    #[test]
    fn scale_test() {
        let instance = Instance::from_file("instances/test.json").unwrap();
        decomposition_approach(&instance);
    }
}
