module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.UniqueFaceRightIndex
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewisePairingRegular
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.PairingHorns

/-!
概要：edgewise の右半分と全境界面を固定する領域の包含は right anodyne。
方針：既存の正則 pairing の挿入頂点より前に、選んだ左頂点が残ることを使う。
規約：Kan 標的への延長から、元の right fibration に対する相対延長へ強める。
使われ方：小さい元の圏と Yoneda slice の大域比較に必要な twisted arrow の相対比較。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 同じ既存 pairing が用いる面の番号は、全て零以外。 -/
lemma edgewiseExtensionPairing_ne_zero (n : ℕ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing.{u} n).II) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing n).isUniquelyCodimOneFace s).index rfl ≠ 0 := by
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s.val.toN
  let hS := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOutsideSimplexEquiv n s.val).property
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot S hS
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.stdSimplexUniqueFace_ne_zero s.val.toN ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing n).p s).val.toN
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing n).isUniquelyCodimOneFace s) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing_support n s)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot_mem S hS, ?_⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n i).val < (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i).val
  dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex]
  have := i.isLt
  omega

/-- 同じ右半分・全境界面の固定領域は、right horn だけの接合で得られる。 -/
lemma edgewiseRightExtensionDomain_rightAnodyne (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightExtensionDomain.{u} n).ι :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pairing_rightAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseExtensionPairing n) (edgewiseExtensionPairing_ne_zero n)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
