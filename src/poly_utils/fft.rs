use std::{collections::HashMap, time::{Duration, Instant}};

use ark_ff::Field;
use ark_poly::{univariate::{DenseOrSparsePolynomial, DensePolynomial}, DenseUVPolynomial, Polynomial};
use ark_ff::Zero;

use super::interpolation::vanishing_poly;

pub const BASE_THRESHOLD: usize = 1;

// TODO: Check BASE_THRESHOLD
// This is a FFT that works where the poly degree is larger than the domain size
pub fn fft<F: Field>(coeffs: &[F], generator: F, coset_offset: F, size: usize) -> Vec<F> {
    if size <= BASE_THRESHOLD {
        let poly = DensePolynomial::from_coefficients_slice(coeffs);
        let mut evaluations = vec![];
        let mut scale = F::ONE;
        for _ in 0..size {
            evaluations.push(poly.evaluate(&(coset_offset * scale)));
            scale *= generator;
        }
        return evaluations;
    }

    let next_power_of_two = (coeffs.len()).next_power_of_two();
    let mut coeffs = coeffs.to_vec();
    coeffs.resize(next_power_of_two, F::ZERO);

    let odd = coeffs
        .iter()
        .skip(1)
        .step_by(2)
        .cloned()
        .collect::<Vec<_>>();
    let even = coeffs.iter().step_by(2).cloned().collect::<Vec<_>>();

    let gen2 = generator * generator;
    let off2 = coset_offset * coset_offset;
    let size2 = size / 2;
    let odd_evals = fft(&odd, gen2, off2, size2);
    let even_evals = fft(&even, gen2, off2, size2);

    let mut res = vec![];
    let mut scale = F::ONE;
    for i in 0..size {
        let even = even_evals[i % even_evals.len()];
        let odd = odd_evals[i % odd_evals.len()];

        res.push(even + (coset_offset * scale) * odd);
        scale *= generator;
    }

    res
}

fn poly_mod<F: Field>(
    f: &DensePolynomial<F>,
    g: &DensePolynomial<F>,
) -> DensePolynomial<F> {
    let a = DenseOrSparsePolynomial::from(f);
    let b = DenseOrSparsePolynomial::from(g);
    let (_, remainder) = a.divide_with_q_and_r(&b).expect("division failed");
    if remainder.is_zero() {
        DensePolynomial::from_coefficients_vec(vec![F::zero()])
    } else {
        remainder
    }
}

pub fn evaluate_polynomial<F: Field>(
    f: &DensePolynomial<F>,
    points: &[F],
) -> Vec<F> {
    if points.is_empty() {
        return Vec::new();
    }
    if points.len() == 1 {
        // return vec![f.evaluate(&points[0])];
        return f.coeffs.clone();
    }

    let mid = points.len() / 2;
    let (x0, x1) = points.split_at(mid);

    let g0 = vanishing_poly(x0);
    let g1 = vanishing_poly(x1);

    let f0 = poly_mod(&f, &g0);
    let f1 = poly_mod(&f, &g1);

    let mut res0 = evaluate_polynomial(&f0, x0);
    let mut res1 = evaluate_polynomial(&f1, x1);

    res0.append(&mut res1);
    res0
}

// struct VanishingTree<F: Field> {
//     layers: Vec<Vec<DensePolynomial<F>>>, // 每层存储该层的所有节点多项式
//     point_range: Vec<Vec<(usize, usize)>>, // 每层节点对应的点集范围 [start, end)
// }

// fn build_vanishing_tree<F: Field>(points: &[F]) -> VanishingTree<F> {
//     let n = points.len();
//     let mut layers = Vec::new();
//     let mut point_ranges = Vec::new();

//     // 第0层：叶子节点（每个点对应一个线性因子）
//     let mut current_layer: Vec<DensePolynomial<F>> = points
//         .iter()
//         .map(|x| DensePolynomial::from_coefficients_slice(&[-*x, F::ONE]))
//         .collect();
//     let mut current_ranges: Vec<(usize, usize)> = (0..n).map(|i| (i, i + 1)).collect();
    
//     layers.push(current_layer.clone());
//     point_ranges.push(current_ranges.clone());

//     // 逐层向上合并，直到只剩一个根节点
//     while current_layer.len() > 1 {
//         let mut next_layer = Vec::new();
//         let mut next_ranges = Vec::new();
//         let mut i = 0;

//         // 两两合并相邻节点
//         while i < current_layer.len() {
//             if i + 1 < current_layer.len() {
//                 let merged_poly = current_layer[i].naive_mul(&current_layer[i + 1]);
//                 let merged_range = (current_ranges[i].0, current_ranges[i + 1].1);
//                 next_layer.push(merged_poly);
//                 next_ranges.push(merged_range);
//                 i += 2;
//             } else {
//                 // 处理奇数节点：直接传递到上层
//                 next_layer.push(current_layer[i].clone());
//                 next_ranges.push(current_ranges[i].clone());
//                 i += 1;
//             }
//         }

//         layers.push(next_layer.clone());
//         point_ranges.push(next_ranges.clone());
//         current_layer = next_layer;
//         current_ranges = next_ranges;
//     }

//     VanishingTree {
//         layers,
//         point_range: point_ranges,
//     }
// }

struct VanishingTreeNode<F: Field> {
    poly: DensePolynomial<F>,  // 当前节点的消失多项式
    start: usize,              // 覆盖的点集起始索引
    end: usize,                // 覆盖的点集结束索引
}

/// 预计算树：HashMap 的键为层级和节点编号
type VanishingTree<F> = HashMap<(usize, usize), VanishingTreeNode<F>>;

/// 构建消失多项式树
fn build_vanishing_tree<F: Field>(points: &[F]) -> VanishingTree<F> {
    let mut tree = VanishingTree::new();
    let n = points.len();

    // 递归构建树的辅助函数
    fn build_layer<F: Field>(
        tree: &mut VanishingTree<F>,
        points: &[F],
        layer: usize,
        node_id: usize,
        start: usize,
        end: usize,
    ) {
        if start >= end {
            return;
        }

        // 当前点集范围对应的消失多项式
        let poly = if start + 1 == end {
            // 叶子节点：(x - x_i)
            DensePolynomial::from_coefficients_slice(&[-points[start], F::ONE])
        } else {
            // 递归构建左右子树
            let mid = (start + end) / 2;
            build_layer(tree, points, layer + 1, 2 * node_id, start, mid);
            build_layer(tree, points, layer + 1, 2 * node_id + 1, mid, end);

            // 合并左右子树的消失多项式
            let left_poly = &tree[&(layer + 1, 2 * node_id)].poly;
            let right_poly = &tree[&(layer + 1, 2 * node_id + 1)].poly;
            left_poly.naive_mul(right_poly)
        };

        // 插入当前节点
        tree.insert(
            (layer, node_id),
            VanishingTreeNode { poly, start, end },
        );
    }

    // 从根节点开始构建（layer=0, node_id=0）
    build_layer(&mut tree, points, 0, 0, 0, n);
    tree
}

pub fn evaluate_polynomial_with_precompute<F: Field>(
    f: &DensePolynomial<F>,
    points: &[F],
    tree: &VanishingTree<F>,    // 预计算的树
    layer: usize,              // 当前层级
    node_id: usize,            // 当前节点编号
) -> Vec<F> {
    if points.is_empty() {
        return Vec::new();
    }

    // 从树中获取当前节点的消失多项式及其覆盖的索引范围
    let node = tree.get(&(layer, node_id)).unwrap();
    assert!(node.start < points.len() && node.end <= points.len());

    if node.start + 1 == node.end {
        // 叶子节点：直接求值
        vec![f.coeffs[0]]
    } else {
        // 获取左右子树的多项式
        //let mid = (node.start + node.end) / 2;
        let left_node = tree.get(&(layer + 1, 2 * node_id)).unwrap();
        let right_node = tree.get(&(layer + 1, 2 * node_id + 1)).unwrap();

        // 取模并递归求值
        let f0 = poly_mod(&f, &left_node.poly);
        let f1 = poly_mod(&f, &right_node.poly);

        let mut res0 = evaluate_polynomial_with_precompute(&f0, points, tree, layer + 1, 2 * node_id);
        let mut res1 = evaluate_polynomial_with_precompute(&f1, points, tree, layer + 1, 2 * node_id + 1);

        res0.append(&mut res1);
        res0
    }
}


#[derive(Default, Debug)]
struct TimeStats {
    vanishing_poly: Duration,
    poly_mod: Duration,
    recursive: Duration,
}

pub fn evaluate_polynomial_with_stats<F: Field>(
    f: &DensePolynomial<F>,
    points: &[F],
    stats: &mut TimeStats,
) -> Vec<F> {
    if points.is_empty() {
        return Vec::new();
    }
    if points.len() == 1 {
        return vec![f.evaluate(&points[0])];
    }

    let mid = points.len() / 2;
    let (x0, x1) = points.split_at(mid);

    // 统计 vanishing_poly 时间
    let start_vanishing = Instant::now();
    let g0 = vanishing_poly(x0);
    let g1 = vanishing_poly(x1);
    stats.vanishing_poly += start_vanishing.elapsed();

    // 统计 poly_mod 时间
    let start_poly_mod = Instant::now();
    let f0 = poly_mod(&f, &g0);
    let f1 = poly_mod(&f, &g1);
    stats.poly_mod += start_poly_mod.elapsed();

    // 统计递归时间
    let start_recursive = Instant::now();
    let mut res0 = evaluate_polynomial_with_stats(&f0, x0, stats);
    let mut res1 = evaluate_polynomial_with_stats(&f1, x1, stats);
    stats.recursive += start_recursive.elapsed();

    res0.append(&mut res1);
    res0
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use crate::domain::Domain;

    use ark_poly::EvaluationDomain;

    use super::*;
    use ark_ff::Field;
    use ark_poly::{univariate::DensePolynomial, Polynomial};
    use ark_std::{test_rng, UniformRand};
    use ark_test_curves::bls12_381::Fr as BlsFr; 

    #[test]
    fn test_evaluate_random_polynomial() {
        let rng = &mut test_rng();

        let degree = 1<<10;
        let coeffs: Vec<BlsFr> = (0..=degree).map(|_| BlsFr::rand(rng)).collect();
        let f = DensePolynomial::from_coefficients_vec(coeffs);

        //let points: Vec<BlsFr> = (0..1<<15).map(|_| BlsFr::rand(rng)).collect();

        let domain = Domain::<BlsFr>::new(
                1<<10,
                1,
            ).unwrap();
        
        let points :Vec<BlsFr> = domain.backing_domain.elements().collect();

        let start = Instant::now();
        let evals = f
            .evaluate_over_domain_by_ref(domain.backing_domain)
            .evals;
        let duration_check3 = start.elapsed();
        println!("fft evaluate_polynomial:{:?}", duration_check3);
        //println!("{:?}",evals[101]);

        let start = Instant::now();
        for (i, &point) in points.iter().enumerate() {
            let expected = f.evaluate(&point);
            // if i == 101 {
            //     println!("{:?}",expected);
            // }
            //assert_eq!(evaluated_values[i], expected);
        }
        let duration_check2 = start.elapsed();
        println!("naive evaluate_polynomial:{:?}", duration_check2);

        // let start = Instant::now();
        // let evaluated_values = evaluate_polynomial(&f, &points);
        // //println!("{:?}",evaluated_values[101]);
        // let duration_check1 = start.elapsed();
        // println!("fast evaluate_polynomial:{:?}", duration_check1);

        let mut stats = TimeStats::default();
        let result = evaluate_polynomial_with_stats(&f, &points, &mut stats);
        println!("{:?}", result[101]);
        println!("Time stats: {:?}", stats);

        let build_tree = Instant::now();
        let tree = build_vanishing_tree(&points);
        let duration = build_tree.elapsed();
        println!("build_tree time:{:?}", duration);
        let eval_time_pre = Instant::now();
        let results = evaluate_polynomial_with_precompute(
            &f, &points, &tree, 
            0,   
            0
        );
        //println!("{:?}", results[101]);
        let duration = eval_time_pre.elapsed();
        println!("evaluate_polynomial_with_precompute time:{:?}", duration);
    }
}