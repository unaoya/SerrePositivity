module

public import SerrePositivity.EInfinity.SimplexCuts.HomogeneousTensorDifferentialTransports

/-!
# 同じ斉次テンソルの次数の族の照合

Berger–Fresse §2.2.7、M14 L09の証明分割。
既存のテンソルと包含を、等しい次数と同じ因子の値で比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A]

/-- C270：同じ次数の族と同じ因子の値を持つ純粋テンソルは異種等式で一致。 -/
lemma tensorValue_heq_degree (K : Complex A) (n : ℕ) (d e : Fin n → ℕ)
    (hd : d = e) (v : ∀ i, K.X (-(d i : ℤ))) (w : ∀ i, K.X (-(e i : ℤ)))
    (hv : ∀ i, HEq (v i) (w i)) : HEq (tensorValue K n d v) (tensorValue K n e w) := by
  subst e
  have he : v = w := by funext i; exact eq_of_heq (hv i)
  subst w
  rfl

/-- C271：同じ三つの次数と同じ因子を持つ斉次包含の値は異種等式で一致。 -/
lemma tensorPair_heq_indices (P Q : Complex A) {i j k i' j' k' : ℤ}
    (h : i + j = k) (h' : i' + j' = k') (hi : i = i') (hj : j = j') (hk : k = k')
    (x : P.X i) (y : Q.X j) (x' : P.X i') (y' : Q.X j')
    (hx : HEq x x') (hy : HEq y y') :
    HEq (ιTensorObj P Q i j k h (x ⊗ₜ[A] y))
      (ιTensorObj P Q i' j' k' h' (x' ⊗ₜ[A] y')) := by
  subst i'
  subst j'
  subst k'
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  rfl

end SerrePositivity.EInfinity.SimplexCuts
