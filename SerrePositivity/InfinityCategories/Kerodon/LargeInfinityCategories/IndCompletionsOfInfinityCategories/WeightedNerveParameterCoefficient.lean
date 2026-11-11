module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedNerveParameter
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveHornCoefficientFaces

/-!
概要：元の相対ホーンの最後の係数評価は、元の固定底のパラメータを保つ。
方針：元の各面の最後の係数と終点への輸送を計算し、係数射影の自然性で戻す。
規約：欠ける面にも底にも追加の充填仮定を置かない。
使われ方：固定底を保つ weighted nerve の相対左ホーン充填。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Category.{u} I] {F : I ⥤ SSet.{u}} {B : SSet.{u}}
  (η : F ⟶ (CategoryTheory.Functor.const I).obj B)

/-- 最後の係数ホーンの元の底への射影は、元のホーンの同じパラメータ射。 -/
lemma weightedNerveHornLastCoefficient_parameter {n : ℕ}
    (σ : ComposableArrows I (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornLastCoefficient F σ k a ha ≫ η.app (σ.obj (Fin.last (n + 1))) =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter η := by
  apply horn.hom_ext'
  intro j hj
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornLastCoefficient_face]
  let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornFaceDiagram F σ k a ha j hj
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
    _ = SSet.yonedaEquiv.symm (⟨σ', τ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter η :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter_yoneda η (⟨σ', τ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n)).symm
    _ = horn.ι k j hj ≫ a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter η := by
      dsimp only [σ', τ]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornFaceDiagram_eta, SSet.yonedaEquiv.symm_apply_apply, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
