module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedNerveParameter
public import SerrePositivity.InfinityCategories.F1.WeightedNerveHornCoefficientFaces

/-!
概要：元の相対ホーンの最後の係数評価は、元の固定底のパラメータを保つ。
方針：元の各面の最後の係数と終点への輸送を計算し、係数射影の自然性で戻す。
規約：欠ける面にも底にも追加の充填仮定を置かない。
使われ方：固定底を保つ weighted nerve の相対左ホーン充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {F : I ⥤ SSet.{u}} {B : SSet.{u}}
  (η : F ⟶ (CategoryTheory.Functor.const I).obj B)

/-- 最後の係数ホーンの元の底への射影は、元のホーンの同じパラメータ射。 -/
lemma weightedNerveHornLastCoefficient_parameter {n : ℕ}
    (σ : ComposableArrows I (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F =
      (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    weightedNerveHornLastCoefficient F σ k a ha ≫ η.app (σ.obj (Fin.last (n + 1))) =
      a ≫ weightedNerveParameter η := by
  apply horn.hom_ext'
  intro j hj
  rw [← Category.assoc, weightedNerveHornLastCoefficient_face]
  let τ := weightedNerveHornFaceDiagram F σ k a ha j hj
  let σ' := (SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ
  calc
    (τ.app (Fin.last n) ≫ F.map (σ.map
        (homOfLE (Fin.le_last ((SimplexCategory.δ j).toOrderHom (Fin.last n)))))) ≫
        η.app (σ.obj (Fin.last (n + 1))) =
      τ.app (Fin.last n) ≫ η.app (σ'.obj (Fin.last n)) := by
        rw [Category.assoc, η.naturality]
        change τ.app (Fin.last n) ≫ η.app (σ'.obj (Fin.last n)) ≫ 𝟙 B = _
        exact congrArg (fun f ↦ τ.app (Fin.last n) ≫ f)
          (Category.comp_id (η.app (σ'.obj (Fin.last n))))
    _ = SSet.yonedaEquiv.symm (⟨σ', τ⟩ : weightedNerveSimplex F n) ≫
        weightedNerveParameter η :=
      (weightedNerveParameter_yoneda η (⟨σ', τ⟩ : weightedNerveSimplex F n)).symm
    _ = horn.ι k j hj ≫ a ≫ weightedNerveParameter η := by
      dsimp only [σ', τ]
      rw [weightedNerveHornFaceDiagram_eta, SSet.yonedaEquiv.symm_apply_apply, Category.assoc]

end SerrePositivity.InfinityCategories.F2.Ind
