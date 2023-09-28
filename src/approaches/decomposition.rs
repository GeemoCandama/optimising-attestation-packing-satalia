use crate::aapp::instance::{Attestation, AttestationData, EpochAttesterID, Instance};
use crate::algorithms::{bron_kerbosh, WeightedMaximumCoverage};
use std::collections::{HashMap, HashSet};
use std::time::{Instant, Duration};
use itertools::Itertools;

pub fn decomposition_approach(instance: &Instance) {
    let start = Instant::now();

    // group attestations by data
    let aggregated_atts = group_by_att_data(&instance.aggregated_attestations);
    let unaggregated_atts = group_by_att_data(&instance.unaggregated_attestations);

    let mut num_cliques = vec![];

    let mut data_vec: Vec<&AttestationData> = vec![];
    let mut cliqued_atts: Vec<Vec<Vec<EpochAttesterID>>> = vec![];

    for (data, attestations) in &aggregated_atts {
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
    let mut f_map: Vec<Vec<f64>> = vec![vec![0.0; 129]; cliqued_atts.len() + 1];
    let mut g_map: Vec<Vec<f64>> = vec![vec![0.0; 129]; cliqued_atts.len() + 1];
    // iterate over vectors of vectors of cliques 
    // index: usize
    // clique_set: Vec<Vec<EpochAttesterID>>
    // one clique is a Vec<EpochAttesterID>

    let mut num_available_atts = 0;
    let m = 128;
    let num_data = cliqued_atts.len();
    let mut mip_time = Duration::new(0, 0);
    for (index, clique_set) in cliqued_atts.iter().enumerate() {
        let index = index + 1;
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
        
        num_available_atts += clique_set.len();
        for i in 0..=m {
            let f_k_m = if i > num_available_atts {
                f_map[index - 1][i]
            } else {
                calculate_f_from_map(
                    instance, 
                    &f_map, 
                    &mut g_map,
                    clique_set, 
                    reindexed_atts.clone(), 
                    reindexed_weights.clone(), 
                    index, 
                    i,
                    &mut mip_time
                )
            };
            f_map[index][i] = f_k_m;
        }
    }

    let optimal_reward = f_map.last().unwrap().last().unwrap();
    println!("optimal_reward: {}", optimal_reward);

    print!("{}", instance.slot.0);

    // print!(
    //     ",{},{}",
    //     &final_attesters
    //         .iter()
    //         .flatten()
    //         .collect::<HashSet<_>>()
    //         .len(),
    //     optimal_reward
    // );
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
        ",total mip time: {:?}, total time: {}",
        mip_time,
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
    instance: &Instance,
    f_map: &Vec<Vec<f64>>,
    g_map: &mut Vec<Vec<f64>>,
    clique_set: &Vec<Vec<EpochAttesterID>>,
    reindexed_atts: Vec<Vec<usize>>,
    reindexed_weights: Vec<f64>,
    k: usize,
    m: usize,
    mip_time: &mut Duration,
) -> f64 {
    let max_domain = std::cmp::min(clique_set.len(), m);
    let mut choices = vec![0.0; max_domain + 1];
    let answer = {
        for q in 0..=max_domain {
            let f_val = if k == 0 || m == 0 {
                0.0
            } else {
                let second_ind = if m - q >= f_map[k - 1].len() {
                    f_map[k - 1].len() - 1
                } else {
                    m - q    
                };
                 f_map[k-1][second_ind]
            };

            let g_val = if k == 0 || q == 0 {
                0.0
            } else if g_map[k][q] == 0.0 {  
                let res = if reindexed_atts.len() == 1 {
                    vec![0]
                } else {
                    let wmcp = WeightedMaximumCoverage {
                        sets: reindexed_atts.clone(),
                        weights: reindexed_weights.clone(),
                        k: q,
                    };
                    let mip_start = Instant::now();
                
                    let res = wmcp.solve().unwrap();
                    let mip_end = Instant::now();
                    *mip_time += mip_end - mip_start;
                    res
                };
                let final_attesters: Vec<Vec<EpochAttesterID>> =
                    res.iter().map(|idx| clique_set[*idx].clone()).collect();

                let g_val = calculate_reward(&final_attesters, &instance.reward_function);
                g_map[k][q] = g_val;
                g_val
            } else {
                g_map[k][q]
            };

            choices[q] = f_val + g_val;
        }
        *choices.iter().max_by(|a, b| a.total_cmp(b)).unwrap()
    };
    answer
}

#[allow(unused_imports)]
mod tests {
    use super::*;
    use crate::{Instance, RawInstance};

    // #[test]
    // fn scale_test() {
    //     let instance = Instance::from_file("instances/test.json").unwrap();
    //     decomposition_approach(&instance);
    // }

    #[test]
    fn test_basic_logic_of_decomposition() {
        // setup the mock attestations by data
        let data_to_atts: Vec<Vec<usize>> = vec![
            (0..4).collect(), 
            (4..8).collect(),
            (8..12).collect(),
            (12..16).collect()
        ];

        // setup mock rewards
        let mut rewards = vec![1; 16];
        rewards[0] += 1;
        rewards[5] += 1;
        rewards[10] += 1;
        rewards[15] += 1;

        let capacity = 4;

        let mut f_map: Vec<Vec<usize>> = vec![vec![0; capacity + 1]; capacity + 1];
        for (index, cliques) in data_to_atts.iter().enumerate() {
            let index = index + 1; 
            for i in 0..=capacity {
                let f_k_m = if i < cliques.len() + 1 {
                    calculate_f_from_map_test(
                        &f_map, 
                        cliques, 
                        index, 
                        i
                    )
                } else {
                    f_map[index][i-1]
                };
                f_map[index][i] = f_k_m;
            }
        }
        let optimal_reward = f_map.last().unwrap().last().unwrap();
        println!("{:?}", f_map);
        println!("{}", optimal_reward);
    }

    fn calculate_f_from_map_test(
        f_map: &Vec<Vec<usize>>,
        clique_set: &Vec<usize>,
        k: usize,
        m: usize,
    ) -> usize {
        let rewards = [2, 1, 1, 1];
        let max_domain = std::cmp::min(clique_set.len(), m);
        let mut choices = vec![0; max_domain + 1];
        if !(k == 0 || m == 0) {
            for q in 0..=max_domain {
                let f_val = if k == 0 || m == 0 {
                    0
                } else {
                    let second_ind = if m - q >= f_map[k - 1].len() {
                        f_map[k - 1].len() - 1
                    } else {
                        m - q    
                    };
                     f_map[k-1][second_ind]
                };
                
                let g_val: usize = rewards[0..q].iter().sum();
    
                choices[q] = f_val + g_val;
            }
            *choices.iter().max().unwrap()
        } else {
            0
        }
    }
}
