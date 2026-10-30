module

public import SerrePositivity.LengthAlgebra.SerreQuotient
public import SerrePositivity.CategoryTheory.Euler

/-! # 長さ付き代数における長完全列の Euler 評価

冪ねじれ性と長さの有限性を確認した加群を実際のアーベル部分圏に入れ、
共通の長完全列の定理を適用する。複体の射影性や Koszul 条件は使わない。
-/

@[expose] public section

universe u

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

set_option backward.isDefEq.respectTransparency false in
/-- 元の加群の長さによる Euler 加法性は、有限長さ部分圏での共通定理の適用である。 -/
theorem normalizedLength_euler_exact_sequence
    (X₁ X₂ X₃ : ℤ → ModuleCat.{u} R)
    (α : ∀ i, X₁ i ⟶ X₂ i) (β : ∀ i, X₂ i ⟶ X₃ i)
    (δ : ∀ i, X₃ i ⟶ X₁ (i + 1))
    {w₂ : ∀ i, α i ≫ β i = 0} {w₃ : ∀ i, β i ≫ δ i = 0}
    {w₁ : ∀ i, δ i ≫ α (i + 1) = 0}
    (h₂ : ∀ i, (ShortComplex.mk (α i) (β i) (w₂ i)).Exact)
    (h₃ : ∀ i, (ShortComplex.mk (β i) (δ i) (w₃ i)).Exact)
    (h₁ : ∀ i, (ShortComplex.mk (δ i) (α (i + 1)) (w₁ i)).Exact)
    (t₁ : ∀ i, IsPowTorsion J (X₁ i)) (t₂ : ∀ i, IsPowTorsion J (X₂ i))
    (t₃ : ∀ i, IsPowTorsion J (X₃ i))
    (l₁ : ∀ i, lam.len (X₁ i) ≠ ⊤) (l₂ : ∀ i, lam.len (X₂ i) ≠ ⊤)
    (l₃ : ∀ i, lam.len (X₃ i) ≠ ⊤)
    (hb₂ : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (X₂ i))
    (hb₃ : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (X₃ i)) :
    (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * (lam.len (X₂ i)).toReal) =
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * (lam.len (X₁ i)).toReal) +
        ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * (lam.len (X₃ i)).toReal := by
  let Y₁ : ℤ → FiniteLengthTorsion lam := fun i ↦ ⟨X₁ i, t₁ i, l₁ i⟩
  let Y₂ : ℤ → FiniteLengthTorsion lam := fun i ↦ ⟨X₂ i, t₂ i, l₂ i⟩
  let Y₃ : ℤ → FiniteLengthTorsion lam := fun i ↦ ⟨X₃ i, t₃ i, l₃ i⟩
  let a : ∀ i, Y₁ i ⟶ Y₂ i := fun i ↦ ObjectProperty.homMk (α i)
  let b : ∀ i, Y₂ i ⟶ Y₃ i := fun i ↦ ObjectProperty.homMk (β i)
  let d : ∀ i, Y₃ i ⟶ Y₁ (i + 1) := fun i ↦ ObjectProperty.homMk (δ i)
  have v₂ (i : ℤ) : a i ≫ b i = 0 := ObjectProperty.hom_ext _ (w₂ i)
  have v₃ (i : ℤ) : b i ≫ d i = 0 := ObjectProperty.hom_ext _ (w₃ i)
  have v₁ (i : ℤ) : d i ≫ a (i + 1) = 0 := ObjectProperty.hom_ext _ (w₁ i)
  apply additiveLength_euler_exact_sequence (finiteLength lam) (finiteLength_iso lam)
    (finiteLength_add lam) (finiteLength_of_isZero lam) Y₁ Y₂ Y₃ a b d
    (w₂ := v₂) (w₃ := v₃) (w₁ := v₁)
  · intro i
    exact (ShortComplex.exact_map_iff_of_faithful _ (finiteLengthTorsion lam).ι).mp (h₂ i)
  · intro i
    exact (ShortComplex.exact_map_iff_of_faithful _ (finiteLengthTorsion lam).ι).mp (h₃ i)
  · intro i
    exact (ShortComplex.exact_map_iff_of_faithful _ (finiteLengthTorsion lam).ι).mp (h₁ i)
  · obtain ⟨a, b, hab⟩ := hb₂
    exact ⟨a, b, fun i hi ↦ IsZero.of_full_of_faithful_of_isZero
      (finiteLengthTorsion lam).ι _ (hab i hi)⟩
  · obtain ⟨a, b, hab⟩ := hb₃
    exact ⟨a, b, fun i hi ↦ IsZero.of_full_of_faithful_of_isZero
      (finiteLengthTorsion lam).ι _ (hab i hi)⟩

end SerrePositivity.LengthAlgebra
