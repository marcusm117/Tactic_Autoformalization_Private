import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem exercise_7_2_12 {R G : Type*} [Ring R] [Group G] [Fintype G] :
  ∑ g : G, MonoidAlgebra.of R G g ∈ center (MonoidAlgebra R G) := by
  classical
  rw [Set.mem_center_iff]
  constructor
  intro x
  refine MonoidAlgebra.induction_on x ?_ ?_ ?_
  · simp
  · intro x y hx hy
    calc
      (x + y) * (∑ g : G, MonoidAlgebra.of R G g) =
          x * (∑ g : G, MonoidAlgebra.of R G g) +
            y * (∑ g : G, MonoidAlgebra.of R G g) := by
          rw [add_mul]
      _ = (∑ g : G, MonoidAlgebra.of R G g) * x +
            (∑ g : G, MonoidAlgebra.of R G g) * y := by
          rw [hx, hy]
      _ = (∑ g : G, MonoidAlgebra.of R G g) * (x + y) := by
          rw [mul_add]
  · intro a r
    calc
      MonoidAlgebra.single a r * (∑ g : G, MonoidAlgebra.of R G g) =
          ∑ g : G, MonoidAlgebra.single (a * g) r := by
            simp [Finset.mul_sum]
      _ = ∑ g : G, MonoidAlgebra.single g r := by
            simpa using
              (Fintype.sum_equiv (Equiv.mulLeft a)
                (fun g : G => MonoidAlgebra.single g r))
      _ = ∑ g : G, MonoidAlgebra.single (g * a) r := by
            symm
            simpa using
              (Fintype.sum_equiv (Equiv.mulRight a)
                (fun g : G => MonoidAlgebra.single g r))
      _ = (∑ g : G, MonoidAlgebra.of R G g) * MonoidAlgebra.single a r := by
            simp [Finset.sum_mul]
