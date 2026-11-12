module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveCoefficientFormula
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveHornDiagrams

/-!
概要：相対ホーンの係数評価の各面を元の重み付き図式から回収する。
方針：ホーン面を Yoneda の単体で表示し直し、係数評価の自然性と明示計算を使う。
規約：最後の頂点を含まない面も、終点への輸送を添えて同じ係数値へ写す。
使われ方：Kerodon §5.3.3（Tag 025W）、係数の Kan 充填と元の weighted nerve のホーンの比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：係数ホーンの j 面は、元の j 面の最後の成分を終点へ輸送した射。
方針：面の底を正規化し、部分単体上の係数評価の計算式を適用する。
規約：j は欠ける面 k 以外の任意の面。
使われ方：Kerodon §5.3.3（Tag 025W）、充填の全ての指定面の一致を確認する中心的な式。 -/
lemma weightedNerveHornLastCoefficient_face {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1)) (k : Fin (n + 2))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (j : Fin (n + 2)) (hj : j ≠ k) :
    horn.ι k j hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornLastCoefficient F σ k a ha =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornFaceDiagram F σ k a ha j hj).app (Fin.last n) ≫
        F.map (σ.map (homOfLE (Fin.le_last ((SimplexCategory.δ j).toOrderHom (Fin.last n))))) := by
  let r := horn.ι k j hj
  let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornFaceDiagram F σ k a ha j hj
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n :=
    ⟨(SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ, τ⟩
  have hs : SSet.yonedaEquiv.symm s = r ≫ a := by
    change (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (n := ⦋n⦌)).symm
      (⟨(SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornFaceDiagram F σ k a ha j hj⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornFaceDiagram_eta]
    exact SSet.yonedaEquiv.symm_apply_apply _
  have hr : (r ≫ a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      (r ≫ (horn (n + 1) k).ι) ≫ SSet.yonedaEquiv.symm σ := by
    rw [Category.assoc, ha, Category.assoc]
  have hb : SSet.yonedaEquiv.symm s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      stdSimplex.δ j ≫ SSet.yonedaEquiv.symm σ :=
    (congrArg (fun q ↦ q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) hs).trans
      (hr.trans (congrArg (fun q ↦ q ≫ (SSet.yonedaEquiv (X := nerve C) (n := ⦋n + 1⦌)).symm σ) (horn.ι_ι k j hj)))
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ (r ≫ a) (r ≫ (horn (n + 1) k).ι) hr :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_precomp F σ a (horn (n + 1) k).ι ha r hr).symm
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ (SSet.yonedaEquiv.symm s) (stdSimplex.δ j) hb :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_congr F σ _ _ _ _ hr hb hs.symm (horn.ι_ι k j hj)
    _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_diagram F σ (SimplexCategory.δ j) τ hb

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
