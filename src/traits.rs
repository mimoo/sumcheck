use ark_ff::Field;
use ark_ff::Zero;
use ark_poly::multivariate::Term;
use ark_poly::multivariate::{SparsePolynomial, SparseTerm};
use ark_poly::MVPolynomial;

pub trait TermSelectedEvaluation<F> {
    fn selected_evaluation(&self, points: &[Option<F>]) -> (F, SparseTerm);
}

impl<F> TermSelectedEvaluation<F> for SparseTerm
where
    F: Field,
{
    fn selected_evaluation(&self, points: &[Option<F>]) -> (F, SparseTerm) {
        let mut scalar = F::one();

        let mut term = vec![];
        for (var, power) in self.iter() {
            match points.get(*var) {
                Some(Some(point)) if point.is_zero() => {
                    return (F::zero(), SparseTerm::new(vec![]));
                }
                Some(Some(point)) => {
                    scalar *= point;
                }
                _ => term.push((*var, *power)),
            };
        }

        (scalar, SparseTerm::new(term))
    }
}

pub trait MultivariateSelectedEvaluation<F> {
    /// Only evaluate selected variables
    fn selected_evaluation(&self, points: &[Option<F>]) -> Self;
}

impl<F> MultivariateSelectedEvaluation<F> for SparsePolynomial<F, SparseTerm>
where
    F: Field,
{
    fn selected_evaluation(&self, points: &[Option<F>]) -> Self {
        assert!(
            points.len() <= self.num_vars(),
            "Invalid number of variables"
        );

        if self.is_zero() {
            return self.clone();
        }

        let mut terms = vec![];
        for (coeff, term) in &self.terms {
            let (new_coeff, new_term) = term.selected_evaluation(points);
            let new_coeff = *coeff * new_coeff;
            terms.push((new_coeff, new_term));
        }

        SparsePolynomial::from_coefficients_vec(self.num_vars(), terms)
    }
}

#[cfg(test)]
pub mod tests {
    use ark_ff::One;
    use ark_pallas::Fq;
    use ark_poly::{multivariate::Term, Polynomial};

    use crate::Poly;

    use super::*;

    pub fn create_poly() -> Poly<Fq> {
        // f(x1, x2, x3) = 3 + 2 * x1 + x2 x3 + x3
        let num_vars = 3;
        let terms = vec![
            // 3
            (Fq::from(3), SparseTerm::new(vec![(0, 0)])),
            // 2 * x1
            (Fq::from(2), SparseTerm::new(vec![(0, 1)])),
            // x2 x3
            (Fq::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
            // x3
            (Fq::from(1), SparseTerm::new(vec![(2, 1)])),
        ];
        SparsePolynomial::from_coefficients_vec(num_vars, terms)
    }

    #[test]
    fn test_multivariate_traits() {
        let poly = create_poly();

        // we evaluate nothing, so we should get the same poly
        let same_poly = poly.selected_evaluation(&[None, None, None]);
        assert_eq!(poly, same_poly);

        // we evaluate x1 with x1 = 1
        let x1_evaluated = poly.selected_evaluation(&[Some(Fq::one()), None, None]);

        // if we try to selectively evaluate x1 again on the result it should do nothing,
        // even with a different value, as we already evaluated x1
        let x1_evaluated_again = x1_evaluated.selected_evaluation(&[Some(Fq::from(2)), None, None]);
        assert_eq!(x1_evaluated, x1_evaluated_again);

        // if we evaluate the original poly with x1 = 1,
        // we should obtain the same result
        let eval1 = x1_evaluated.evaluate(&vec![Fq::one(), Fq::one(), Fq::one()]);
        let eval2 = poly.evaluate(&vec![Fq::one(), Fq::one(), Fq::one()]);
        assert_eq!(eval1, eval2);

        // if we evaluate the semi-evaluated poly with x1 = 2,
        // it should be the same as if we evaluated it with x1 = 1
        let eval3 = x1_evaluated.evaluate(&vec![Fq::from(2), Fq::one(), Fq::one()]);
        assert_eq!(eval1, eval3);
    }
}
