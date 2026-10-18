module

public import SerrePositivity.KST.Comparison.StrictCylinderFibration
public import SerrePositivity.KST.Comparison.HomotopyPullbackSymmetry
public import SerrePositivity.KST.Comparison.FibrantPullbackComparison

/-!
# 二重写像円筒の三頂点のホモトピー引き戻し性の厳密な場合

概要：厳密な引き戻しの span の三つの縦射が Kan fibration なら、円筒への三頂点の四角形はホモトピー引き戻し。
方針：円筒の比較の Kan 条件と、三頂点の厳密な引き戻し、脚の交換の不変性を使う。
規約：Segal 1974 Lemma 1.7 の厳密な場合。二面をホモトピー引き戻しだけへ弱める論証は残る。
使われ方：Segal の貼り合わせの証明における厳密な場合の基礎。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：二面が厳密な引き戻しで三縦射が Kan fibration の span は、円筒への三つのホモトピー引き戻しを与える。
方針：全体の比較の Kan 性を証明済みの厳密な各引き戻しに適用し、脚の交換を戻す。
規約：Segal Lemma 1.7 の一般の場合の証明済みとは主張しない。
使われ方：ホモトピー引き戻しの仮定からの還元先。
-/
theorem doubleMappingCylinder_homotopyPullbacks_of_strict {C A B C' A' B' : SSet.{u}}
    {f : C ⟶ A} {g : C ⟶ B} {f' : C' ⟶ A'} {g' : C' ⟶ B'}
    {c : C ⟶ C'} {a : A ⟶ A'} {b : B ⟶ B'}
    (hf : IsPullback f c a f') (hg : IsPullback g c b g')
    (hc : SSet.modelCategoryQuillen.J.rlp c)
    (ha : SSet.modelCategoryQuillen.J.rlp a)
    (hb : SSet.modelCategoryQuillen.J.rlp b) :
    IsHomotopyPullback (doubleMappingCylinder_left_isPullback hf hg).toCommSq ∧
      IsHomotopyPullback (doubleMappingCylinder_right_isPullback hf hg).toCommSq ∧
      IsHomotopyPullback (doubleMappingCylinder_center_isPullback hf hg).toCommSq := by
  have hm := doubleMappingCylinderMap_rlp hf hg hc ha hb
  refine ⟨?_, ?_, ?_⟩
  · exact isHomotopyPullback_of_left_fibration (doubleMappingCylinder_left_isPullback hf hg) hm
  · exact isHomotopyPullback_of_left_fibration (doubleMappingCylinder_right_isPullback hf hg) hm
  · exact isHomotopyPullback_of_left_fibration (doubleMappingCylinder_center_isPullback hf hg) hm

end SerrePositivity.KST.Comparison
