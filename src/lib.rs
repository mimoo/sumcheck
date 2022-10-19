use ark_ff::Field;
use ark_poly::multivariate::{SparsePolynomial, SparseTerm};
use ark_poly::{MVPolynomial, Polynomial};
use hypercube::HyperCube;
use traits::MultivariateSelectedEvaluation;

pub mod hypercube;
pub mod traits;

type Poly<F> = SparsePolynomial<F, SparseTerm>;

// Note: the notation follows the hyperplonk paper

//
// Data structures
//

// TODO: implement real polynomial commitment
pub struct PolynomialCommitment<F: Field>(Poly<F>);

impl<F> PolynomialCommitment<F>
where
    F: Field,
{
    pub fn commit(poly: &Poly<F>) -> Self {
        Self(poly.clone())
    }

    pub fn evaluate(&self, point: &Vec<F>) -> F {
        self.0.evaluate(point)
    }
}

#[derive(Default)]
pub struct SumCheckParams<F> {
    phantom: std::marker::PhantomData<F>,
}

pub struct SumCheckProof<F>
where
    F: Field,
{
    poly: PolynomialCommitment<F>,
    reduced_polys: Vec<PolynomialCommitment<F>>,
}

impl<F> SumCheckProof<F>
where
    F: Field,
{
    pub fn len(&self) -> usize {
        self.reduced_polys.len()
    }

    pub fn is_empty(&self) -> bool {
        self.reduced_polys.is_empty()
    }
}

//
// Prover
//

impl<F> SumCheckParams<F>
where
    F: Field,
{
    // TODO: prologue should be a digest or a hash state or even beter: a sponge state
    /// Returns the sum, as well as the proof.
    pub fn run_protocol(&self, prologue: (), poly: &Poly<F>) -> (F, SumCheckProof<F>) {
        // compute the sum
        let sum = {
            let num_vars = poly.num_vars();
            let hypercube = HyperCube::new(num_vars, F::one());
            let mut result = F::zero();
            for vars in hypercube {
                result += poly.evaluate(&vars);
            }
            result
        };

        let mut polys = vec![];
        let mut challenges = vec![];
        let mut target = sum;

        let mut num = poly.num_vars();
        while num != 0 {
            num = num - 1;

            // -> reduced poly (`r_i`)
            let new_poly = self.round(target, &poly, num, &challenges);

            if num > 0 {
                // <- challenge (`alpha_i`)
                let challenge_alpha = F::from(7u32); // TODO: sample challenge via fiat-shamir
                challenges.insert(0, challenge_alpha);

                // update next round target (`v <- r_i(alpha_i)`)
                let input = {
                    let mut input = vec![F::zero(); num];
                    input.extend(&challenges);

                    assert_eq!(input.len(), poly.num_vars());
                    input
                };
                target = new_poly.evaluate(&input);
            }

            // store the reduced polynomial for proof
            polys.push(new_poly);
        }

        // commit to all the rounds' polynomials
        let mut commitments = vec![];
        for poly in polys {
            commitments.push(PolynomialCommitment::commit(&poly));
        }

        // return a proof
        (
            sum,
            SumCheckProof {
                poly: PolynomialCommitment::commit(poly),
                reduced_polys: commitments,
            },
        )
    }

    /// Note: challenges are expected to be passed in reverse order.
    fn round(&self, target: F, poly: &Poly<F>, num: usize, challenges: &[F]) -> Poly<F> {
        let new_poly = if num == 0 {
            let mut vars = vec![None]; // the free variable
            vars.extend(challenges.iter().cloned().map(Some));
            poly.selected_evaluation(&vars)
        } else {
            let hypercube = HyperCube::new(num, F::one());

            //                            challenges
            //                             <------->
            // `sum f(0..2, 0..2, 0..2, _, alphas...)`
            //        <-------------->
            //               num
            //
            let mut new_poly = Poly::<F>::from_coefficients_vec(poly.num_vars(), vec![]);
            for vars in hypercube {
                let mut vars: Vec<_> = vars.into_iter().map(Some).collect();
                vars.push(None); // the free variable
                vars.extend(challenges.iter().cloned().map(Some));
                new_poly = new_poly + poly.selected_evaluation(&vars);
            }

            new_poly
        };

        // check that it matches the target
        if cfg!(debug_assertions) {
            let mut zero_input = vec![F::zero(); num];
            let mut one_input = zero_input.clone();

            zero_input.push(F::zero());
            one_input.push(F::one());

            zero_input.extend(challenges);
            one_input.extend(challenges);

            assert_eq!(zero_input.len(), one_input.len());
            assert_eq!(zero_input.len(), poly.num_vars());

            let res = new_poly.evaluate(&zero_input) + new_poly.evaluate(&one_input);
            assert_eq!(target, res);
        }

        new_poly
    }
}

//
// Verifier
//

impl<F> SumCheckParams<F>
where
    F: Field,
{
    // TODO: prologue should be a digest or a hash state or even beter: a sponge state
    pub fn verify(&self, prologue: (), sum: F, num_vars: usize, proof: SumCheckProof<F>) -> bool {
        if proof.len() != num_vars {
            println!(
                "proof length mismatch, got {} commitments, expected {num_vars}",
                proof.len()
            );
            return false;
        }

        let mut challenges = vec![];
        let mut target = sum;

        let mut num = num_vars;
        for reduced_poly in &proof.reduced_polys {
            num = num - 1;

            dbg!("verifying reduced poly");
            // verify that it matches the target
            let mut zero_input = vec![F::zero(); num];
            let mut one_input = zero_input.clone();

            zero_input.push(F::zero());
            one_input.push(F::one());

            zero_input.extend(&challenges);
            one_input.extend(&challenges);

            assert_eq!(zero_input.len(), one_input.len());
            assert_eq!(zero_input.len(), num_vars);

            let res = reduced_poly.evaluate(&zero_input) + reduced_poly.evaluate(&one_input);
            assert_eq!(target, res);

            // <- challenge (`alpha_i`)
            let challenge_alpha = F::from(7u32); // TODO: sample challenge via fiat-shamir
            challenges.insert(0, challenge_alpha);

            // update next round target (`v <- r_i(alpha_i)`)
            let input = {
                let mut input = vec![F::zero(); num];
                input.extend(&challenges);

                assert_eq!(input.len(), num_vars);
                input
            };
            target = reduced_poly.evaluate(&input);
        }

        //
        true
    }
}

#[cfg(test)]
mod test {
    use ark_ff::{One, Zero};
    use ark_pallas::Fq;
    use ark_poly::Polynomial;

    use super::*;

    #[test]
    fn test_multivariate_poly() {
        let poly = crate::traits::tests::create_poly();

        // f(2, 1, 1) = 9
        let res = poly.evaluate(&vec![Fq::from(2), Fq::one(), Fq::one()]);
        assert_eq!(res, Fq::from(9));
    }

    #[test]
    fn test_sumcheck_round_1() {
        // f(x1, x2, x3) = 3 + 2 * x1 + x2 x3 + x3
        let poly = crate::traits::tests::create_poly();

        // f(0,0,0) + f(0,0,1) + f(0,1,0) + f(0,1,1) + ...
        let target = {
            let o = Fq::zero();
            let i = Fq::one();

            // f(0,0,0)
            assert_eq!(poly.evaluate(&vec![o, o, o]), Fq::from(3));
            let mut target = 3;

            // f(1,0,0) + f(0,1,0) + f(0,0,1)
            assert_eq!(poly.evaluate(&vec![i, o, o]), Fq::from(3 + 2));
            assert_eq!(poly.evaluate(&vec![o, i, o]), Fq::from(3));
            assert_eq!(poly.evaluate(&vec![o, o, i]), Fq::from(3 + 1));
            target += (3 + 2) + (3) + (3 + 1);

            // f(1,1,0) + f(0,1,1) + f(1,0,1)
            assert_eq!(poly.evaluate(&vec![i, i, o]), Fq::from(3 + 2));
            assert_eq!(poly.evaluate(&vec![o, i, i]), Fq::from(3 + 1 + 1));
            assert_eq!(poly.evaluate(&vec![i, o, i]), Fq::from(3 + 2 + 1));
            target += (3 + 2) + (3 + 1 + 1) + (3 + 2 + 1);

            // f(1,1,1)
            assert_eq!(poly.evaluate(&vec![i, i, i]), Fq::from(3 + 2 + 1 + 1));
            target + 3 + 2 + 1 + 1
        };

        let num = 2;
        let sumcheck: SumCheckParams<Fq> = SumCheckParams::default();
        sumcheck.round(Fq::from(target), &poly, num, &[]);
    }

    #[test]
    fn test_sumcheck_round_2() {
        // f(x1, x2, x3) = 3 + 2 * x1 + x2 x3 + x3
        let poly = crate::traits::tests::create_poly();
        let alpha = 7; // challenge alpha

        let o = Fq::zero();
        let i = Fq::one();
        let a = Fq::from(alpha);

        // f(0,0,a) + f(0,0,a) + f(0,1,a) + f(0,1,a) + ...
        let target = {
            // f(0,0,a)
            assert_eq!(poly.evaluate(&vec![o, o, a]), Fq::from(3 + alpha));
            let mut target = 3 + alpha;

            // f(1,0,a) + f(0,1,a)
            assert_eq!(poly.evaluate(&vec![i, o, a]), Fq::from(3 + 2 + alpha));
            assert_eq!(poly.evaluate(&vec![o, i, a]), Fq::from(3 + alpha + alpha));
            target += (3 + 2 + alpha) + (3 + alpha + alpha);

            // f(1,1,a)
            assert_eq!(
                poly.evaluate(&vec![i, i, a]),
                Fq::from(3 + 2 + alpha + alpha)
            );
            target + 3 + 2 + alpha + alpha
        };

        let num = 1;
        let sumcheck: SumCheckParams<Fq> = SumCheckParams::default();
        sumcheck.round(Fq::from(target), &poly, num, &[a]);
    }

    #[test]
    fn test_sumcheck_protocol() {
        // f(x1, x2, x3) = 3 + 2 * x1 + x2 x3 + x3
        let poly = crate::traits::tests::create_poly();

        let sumcheck: SumCheckParams<Fq> = SumCheckParams::default();

        let (sum, proof) = sumcheck.run_protocol((), &poly);

        let res = sumcheck.verify((), sum, poly.num_vars(), proof);

        assert!(res);
    }
}
