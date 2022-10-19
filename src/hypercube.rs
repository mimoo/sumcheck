use ark_ff::Field;

pub struct HyperCube<F> {
    max_value: F,
    current: Vec<F>,
    ended: bool,
}

impl<F> HyperCube<F> {
    pub fn new(num_vars: usize, max_value: F) -> Self
    where
        F: Field,
    {
        Self {
            max_value,
            current: vec![F::zero(); num_vars],
            ended: false,
        }
    }
}

impl<F> Iterator for HyperCube<F>
where
    F: Field,
{
    type Item = Vec<F>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.ended {
            return None;
        }

        // get the result to return
        let result = self.current.clone();

        // pre-compute next result
        let mut incremented_a_var = false;
        for var in &mut self.current {
            if *var < self.max_value {
                *var += F::one();
                incremented_a_var = true;
                break;
            } else {
                *var = F::zero();
            }
        }

        if !incremented_a_var {
            self.ended = true;
            self.current = vec![];
        }

        // return result
        Some(result)
    }
}

#[cfg(test)]
mod tests {
    use ark_ff::{One, Zero};
    use ark_pallas::Fq;

    use super::*;

    #[test]
    fn test_hypercube() {
        let o = Fq::zero();
        let i = Fq::one();

        let mut hypercube = HyperCube::new(3, i);

        assert_eq!(hypercube.next(), Some(vec![o, o, o]));
        assert_eq!(hypercube.next(), Some(vec![i, o, o]));
        assert_eq!(hypercube.next(), Some(vec![o, i, o]));
        assert_eq!(hypercube.next(), Some(vec![i, i, o]));
        assert_eq!(hypercube.next(), Some(vec![o, o, i]));
        assert_eq!(hypercube.next(), Some(vec![i, o, i]));
        assert_eq!(hypercube.next(), Some(vec![o, i, i]));
        assert_eq!(hypercube.next(), Some(vec![i, i, i]));
        assert_eq!(hypercube.next(), None);
    }
}
