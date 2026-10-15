module

public import SerrePositivity.CategoryTheory.AlternatingSum
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # 長完全列に共通する Euler 加法性

長さ付きアーベル圏の長完全列を像の短完全列に分け、交代和を取る。
三角圏のホモロジー評価と、具体的な複体の写像錐で同じ定理を使う。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {A : Type*} [Category* A] [Abelian A] (l : A → ℝ)
  (hi : ∀ {X Y : A}, (X ≅ Y) → l X = l Y)
  (ha : ∀ {S : ShortComplex A}, S.ShortExact → l S.X₂ = l S.X₁ + l S.X₃)

include hi ha in
/-- 完全列の中央の評価は両側の射の像の評価の和である。 -/
lemma additiveLength_exact_images {S : ShortComplex A} (hS : S.Exact) :
    l S.X₂ = l (Abelian.image S.f) + l (Abelian.image S.g) := by
  let S' := ShortComplex.mk (Abelian.image.ι S.f) S.g (Abelian.image_ι_comp_eq_zero S.zero)
  have hS' : S'.Exact := (S.exact_iff_exact_image_ι).mp hS
  let S'' := ShortComplex.mk S'.f (Abelian.coimage.π S'.g)
    (Abelian.comp_coimage_π_eq_zero S'.zero)
  have hS'' : S''.ShortExact := { exact := (S'.exact_iff_exact_coimage_π).mp hS' }
  have h := ha hS''
  change l S.X₂ = l (Abelian.image S.f) + l (Abelian.coimage S.g) at h
  rw [hi (Abelian.coimageIsoImage S.g)] at h
  exact h

include hi ha in
/-- 長完全列の Euler 加法性。第二・第三の対象列の有界性だけで十分であり、
射影性・長さの正値性・三角圏から来ることは仮定しない。 -/
lemma additiveLength_euler_exact_sequence
    (hz : ∀ X : A, IsZero X → l X = 0)
    (X₁ X₂ X₃ : ℤ → A)
    (α : ∀ i, X₁ i ⟶ X₂ i) (β : ∀ i, X₂ i ⟶ X₃ i)
    (δ : ∀ i, X₃ i ⟶ X₁ (i + 1))
    {w₂ : ∀ i, α i ≫ β i = 0} {w₃ : ∀ i, β i ≫ δ i = 0}
    {w₁ : ∀ i, δ i ≫ α (i + 1) = 0}
    (h₂ : ∀ i, (ShortComplex.mk (α i) (β i) (w₂ i)).Exact)
    (h₃ : ∀ i, (ShortComplex.mk (β i) (δ i) (w₃ i)).Exact)
    (h₁ : ∀ i, (ShortComplex.mk (δ i) (α (i + 1)) (w₁ i)).Exact)
    (hb₂ : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (X₂ i))
    (hb₃ : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (X₃ i)) :
    (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * l (X₂ i)) =
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * l (X₁ i)) +
        ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * l (X₃ i) := by
  let a := fun i ↦ l (Abelian.image (α i))
  let b := fun i ↦ l (Abelian.image (β i))
  let d := fun i ↦ l (Abelian.image (δ i))
  have hfa : Function.HasFiniteSupport a := by
    obtain ⟨p, q, hpq⟩ := hb₂
    apply (Set.finite_Icc p q).subset
    intro i hi
    by_contra hn
    exact hi (hz _ (IsZero.of_mono (Abelian.image.ι (α i))
      (hpq i (by simp only [Set.mem_Icc] at hn; omega))))
  have hfb : Function.HasFiniteSupport b := by
    obtain ⟨p, q, hpq⟩ := hb₃
    apply (Set.finite_Icc p q).subset
    intro i hi
    by_contra hn
    exact hi (hz _ (IsZero.of_mono (Abelian.image.ι (β i))
      (hpq i (by simp only [Set.mem_Icc] at hn; omega))))
  have hfd : Function.HasFiniteSupport d := by
    obtain ⟨p, q, hpq⟩ := hb₃
    apply (Set.finite_Icc p q).subset
    intro i hi
    by_contra hn
    exact hi (hz _ (IsZero.of_epi (Abelian.factorThruImage (δ i))
      (hpq i (by simp only [Set.mem_Icc] at hn; omega))))
  have h₂ (i : ℤ) : l (X₂ i) = a i + b i :=
    additiveLength_exact_images l hi ha (h₂ i)
  have h₃ (i : ℤ) : l (X₃ i) = b i + d i :=
    additiveLength_exact_images l hi ha (h₃ i)
  have h₁ (i : ℤ) : l (X₁ i) = d (i - 1) + a i := by
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
    rw [add_sub_cancel_right]
    exact additiveLength_exact_images l hi ha (h₁ j)
  simp_rw [h₂, h₁, h₃]
  simpa only [zsmul_eq_mul] using alternatingGroupFinsum_exact a b d hfa hfb hfd

end SerrePositivity
