module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationCornerRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCoconeNaturality
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationLiftedCocone
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowNormalizedPrismCurry
public import SerrePositivity.InfinityCategories.F2.Ind.RightTensorCurryMap

/-!
概要：補間族の元の試験族への全制限を、同じ再構成円柱と余錐として回収する。
方針：全円柱の比較同型の自然性と実補間領域上の一致を curry する。
規約：同じ元の全変換を保持。使われ方：元の comma 族との同型と余錐輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)
local notation "r" => Iso.inv (arrowInterpolationCoconeIso _) ≫
  sliceOverUncurry (arrowInterpolationCornerInclusion _ ≫ V.slicePrism.val)

/-- 元の試験族側の補間全円柱は、同じ slice 円柱からの再構成そのもの。 -/
lemma indArrowInterpolationSquare_restrict :
    (joinMap ((SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0])) (𝟙 Δ[0]) ▷ Δ[1]) ≫
      indArrowInterpolationSquare V = r := by
  rw [indArrowInterpolationSquare, ← Category.assoc,
    arrowInterpolationCoconeIso_inv_naturality, Category.assoc,
    ← sliceOverUncurry_precomp, indArrowInterpolationGlue_restrict]

/-- 元の試験族側の全余錐は、同じ再構成円柱の curry を元の宇宙へ戻したもの。 -/
lemma indArrowInterpolationLiftedCoconeMap_restrict :
    joinMap ((SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0])) (𝟙 Δ[0]) ≫
      indArrowInterpolationLiftedCoconeMap V =
    curry ((β_ (Δ[1] : SSet.{u + 1})
      (join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0])).hom ≫ r) ≫
        arrowDiagramUniverseRestriction (IndInfinity κ C) := by
  rw [indArrowInterpolationLiftedCoconeMap, ← Category.assoc,
    indArrowInterpolationCoherentCoconeMap, rightTensorCurry_precomp,
    indArrowInterpolationSquare_restrict]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
