module

public import SerrePositivity.InfinityCategories.F2.Ind.UniqueFaceRightIndex
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewisePairingRegular
public import SerrePositivity.InfinityCategories.Core.PairingHorns

/-!
概要：edgewise の右半分と全境界面を固定する領域の包含は right anodyne。
方針：既存の正則 pairing の挿入頂点より前に、選んだ左頂点が残ることを使う。
規約：Kan 標的への延長から、元の right fibration に対する相対延長へ強める。
使われ方：小さい元の圏と Yoneda slice の大域比較に必要な twisted arrow の相対比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ既存 pairing が用いる面の番号は、全て零以外。 -/
lemma edgewiseExtensionPairing_ne_zero (n : ℕ) (s : (edgewiseExtensionPairing.{u} n).II) :
    ((edgewiseExtensionPairing n).isUniquelyCodimOneFace s).index rfl ≠ 0 := by
  let S := stdSimplexNondegenerateSupport s.val.toN
  let hS := (edgewiseOutsideSimplexEquiv n s.val).property
  let i := edgewiseSupportPivot S hS
  apply stdSimplexUniqueFace_ne_zero s.val.toN ((edgewiseExtensionPairing n).p s).val.toN
    ((edgewiseExtensionPairing n).isUniquelyCodimOneFace s) (edgewiseRightVertex n i)
    (edgewiseExtensionPairing_support n s)
  refine ⟨edgewiseLeftVertex n i, edgewiseSupportPivot_mem S hS, ?_⟩
  change (edgewiseLeftVertex n i).val < (edgewiseRightVertex n i).val
  dsimp [edgewiseLeftVertex, edgewiseRightVertex]
  have := i.isLt
  omega

/-- 同じ右半分・全境界面の固定領域は、right horn だけの接合で得られる。 -/
lemma edgewiseRightExtensionDomain_rightAnodyne (n : ℕ) :
    rightAnodyneExtensions (edgewiseRightExtensionDomain.{u} n).ι :=
  pairing_rightAnodyneExtensions (edgewiseExtensionPairing n) (edgewiseExtensionPairing_ne_zero n)

end SerrePositivity.InfinityCategories.F2.Ind
