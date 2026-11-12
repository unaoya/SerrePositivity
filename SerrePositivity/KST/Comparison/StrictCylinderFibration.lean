module

public import SerrePositivity.KST.Comparison.FiniteOperationsFibrations
public import SerrePositivity.KST.Comparison.StrictCylinderPullbacks

/-!
# 厳密な引き戻しの span の二重写像円筒の Kan fibration

概要：span の二つの面が厳密な引き戻しで、三つの縦射が Kan fibration なら、円筒の比較も Kan fibration。
方針：中央と端点の余積の引き戻しを用い、pushout の単体ごとの Kan 条件を適用する。
規約：Segal 1974 Lemma 1.7 の厳密な場合。ホモトピー引き戻しの仮定への弱化は別項目。
使われ方：厳密な貼り合わせのホモトピー引き戻しへの接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial

/--
概要：厳密な引き戻しの span の三つの Kan fibration は、二重写像円筒の Kan fibration を誘導する。
方針：中央と端点の余積の引き戻し、直積と余積の Kan 条件、pushout の局所性を使う。
規約：全ての仮定は元の span の縦射と二つの実際の引き戻し。
使われ方：三つの頂点のホモトピー引き戻し性の厳密な場合。
-/
theorem doubleMappingCylinderMap_rlp {C A B C' A' B' : SSet.{u}}
    {f : C ⟶ A} {g : C ⟶ B} {f' : C' ⟶ A'} {g' : C' ⟶ B'}
    {c : C ⟶ C'} {a : A ⟶ A'} {b : B ⟶ B'}
    (hf : IsPullback f c a f') (hg : IsPullback g c b g')
    (hc : SSet.modelCategoryQuillen.J.rlp c)
    (ha : SSet.modelCategoryQuillen.J.rlp a)
    (hb : SSet.modelCategoryQuillen.J.rlp b) :
    SSet.modelCategoryQuillen.J.rlp
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf.w.symm hg.w.symm) := by
  have h := doubleMappingCylinderMap_isPullback hf hg
  exact kanFibration_of_pushoutCover
    (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C') (coprod.map f' g'))
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap f g f' g' c a b hf.w.symm hg.w.symm)
    (c ▷ Δ[1]) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f g) h.1
    (coprod.map a b) (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C) (coprod.map f g)) h.2
    (tensorRight_rlp c hc Δ[1]) (coproductMap_rlp a b ha hb)

end SerrePositivity.KST.Comparison
