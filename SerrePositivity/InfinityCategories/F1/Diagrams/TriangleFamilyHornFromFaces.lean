module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TetrahedronFamilyFilling

/-!
概要：二つの短辺を厳密に回収する全二胞体族は、指定された全内ホーンを回収する。
方針：既存の全族転置で horn の外延性を適用する。
規約：パラメーター B は任意。充填性を要求しない。
使われ方：再構成全族を元の固定ホーンの fiber へ登録する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma triangleFamily_horn_of_faces {X B : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ B ⟶ X) (a : (Λ[2, 1] : SSet.{u}) ⊗ B ⟶ X)
    (h₀ : (stdSimplex.δ (0 : Fin 3) ▷ B) ≫ F = (horn₂₁.ι₁₂ ▷ B) ≫ a)
    (h₂ : (stdSimplex.δ (2 : Fin 3) ▷ B) ≫ F = (horn₂₁.ι₀₁ ▷ B) ≫ a) :
    ((horn 2 (1 : Fin 3)).ι ▷ B) ≫ F = a := by
  apply (familyRightTranspose (Λ[2, 1] : SSet.{u}) B X).injective
  rw [familyRightTranspose_precomp]
  apply horn.hom_ext'
  intro j hj
  rw [← Category.assoc, horn.ι_ι]
  fin_cases j
  · have h := congrArg (familyRightTranspose (Δ[1] : SSet.{u}) B X) h₀
    simp only [familyRightTranspose_precomp] at h
    exact h
  · exact False.elim (hj rfl)
  · have h := congrArg (familyRightTranspose (Δ[1] : SSet.{u}) B X) h₂
    simp only [familyRightTranspose_precomp] at h
    exact h

end SerrePositivity.InfinityCategories
