module

public import SerrePositivity.CategoryTheory.ScalarSupport

/-! # 零写像の錐では消去スカラーの指数を増やさなくてよい -/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C]
  [Linear R C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [Pretriangulated C]

/-- 第一射が零で、スカラーが両端で零なら、錐でも同じスカラーが零。 -/
lemma scalar_zero_on_zero_cone (T : Triangle C) (hT : T ∈ distTriang C)
    (hf : T.mor₁ = 0) (a : R)
    (h₁ : a • 𝟙 T.obj₁ = 0) (h₂ : a • 𝟙 T.obj₂ = 0) :
    a • 𝟙 T.obj₃ = 0 := by
  obtain ⟨e, _⟩ := exists_iso_binaryBiproduct_of_distTriang T.rotate
    (rot_of_distTriang T hT) (by
      change -T.mor₁⟦(1 : ℤ)⟧' = 0
      rw [hf, Functor.map_zero, neg_zero])
  change T.obj₃ ≅ T.obj₂ ⊞ T.obj₁⟦(1 : ℤ)⟧ at e
  have h₁' : a • 𝟙 (T.obj₁⟦(1 : ℤ)⟧) = 0 := by
    have h := congrArg (shiftFunctor C (1 : ℤ)).map h₁
    rw [Functor.map_smul, (shiftFunctor C (1 : ℤ)).map_id, Functor.map_zero] at h
    exact h
  have hb : a • 𝟙 (T.obj₂ ⊞ T.obj₁⟦(1 : ℤ)⟧) = 0 := by
    apply biprod.hom_ext
    · calc
        _ = biprod.fst ≫ (a • 𝟙 T.obj₂) := by simp
        _ = _ := by rw [h₂]; simp
    · calc
        _ = biprod.snd ≫ (a • 𝟙 (T.obj₁⟦(1 : ℤ)⟧)) := by simp
        _ = _ := by rw [h₁']; simp
  apply (cancel_mono e.hom).mp
  calc
    _ = e.hom ≫ (a • 𝟙 _) := by simp
    _ = _ := by rw [hb]; simp

end SerrePositivity
