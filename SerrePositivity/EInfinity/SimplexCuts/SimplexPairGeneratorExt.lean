module

public import SerrePositivity.EInfinity.SimplexCuts.SimplexGeneratorLinearExt
public import SerrePositivity.EInfinity.SimplexCuts.CochainAction

/-!
# χ係数と一般正規化単体の二入力外延性

Berger–Fresse §1.2.1・§2.2.6、M14 L15/L17、報告 §390。
全整数の同じ斉次成分を語基底と全単体で判定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial

/-- 同じ係数と単体の全複体射は全基底値で決まる（BF §2.2.6）。 -/
lemma coefficient_simplex_pair_hom_ext (A : Type u) [CommRing A] (S : SSet.{0}) (m : ℕ)
    {K : Complex A} {f g : Surjection.complex A m ⊗ chains A S ⟶ K}
    (h : ∀ (d q : ℕ) (u : Surjection.BasisWord m d) (x : S _⦋q⦌),
      f.f (-((d + q : ℕ) : ℤ))
        (ιTensorObj (Surjection.complex A m) (chains A S) (-(d : ℤ)) (-(q : ℤ))
          (-((d + q : ℕ) : ℤ)) (by omega)
          ((Surjection.complexXIso A m d).inv
            (Surjection.basis A m d (ULift.up u)) ⊗ₜ[A] gen A S q x)) =
      g.f (-((d + q : ℕ) : ℤ))
        (ιTensorObj (Surjection.complex A m) (chains A S) (-(d : ℤ)) (-(q : ℤ))
          (-((d + q : ℕ) : ℤ)) (by omega)
          ((Surjection.complexXIso A m d).inv
            (Surjection.basis A m d (ULift.up u)) ⊗ₜ[A] gen A S q x))) : f = g := by
  apply HomologicalComplex.hom_ext
  intro z
  apply mapBifunctor.hom_ext
  intro i j hij
  change i + j = z at hij
  by_cases hi : 0 < i
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    simp only [Surjection.complex_eq_zero_of_positive A m i hi a, map_zero]
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, i = -(d : ℤ) := ⟨(-i).toNat, by omega⟩
  by_cases hj : 0 < j
  · have hz : Limits.IsZero ((chains A S).X j) := by
      apply HomologicalComplex.isZero_extend_X
      intro q
      change -(q : ℤ) ≠ j
      omega
    let _ := ModuleCat.isZero_iff_subsingleton.mp hz
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    have hb : b = 0 := Subsingleton.elim _ _
    simp only [hb, map_zero]
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = -(q : ℤ) := ⟨(-j).toNat, by omega⟩
  have he : z = -((d + q : ℕ) : ℤ) := by omega
  subst he
  apply ModuleCat.hom_ext
  apply TensorProduct.curry_injective
  apply IntervalCuts.complex_basis_linear_ext A m d
  intro u
  apply chains_generator_linear_ext A S q
  exact h d q u

end SerrePositivity.EInfinity.SimplexCuts
