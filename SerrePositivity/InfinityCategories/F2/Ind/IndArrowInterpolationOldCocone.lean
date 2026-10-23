module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationSquareRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationCommaFamily
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaSliceFullyFaithful

/-!
概要：補間した実 comma 族の元の試験族上の全余錐を、再構成円柱として回収する。
方針：同じ族の slice uncurry を制限し、実証済みの全円柱の制限式へ戻す。
規約：同じ元の全変換を保持。使われ方：両固定境界の比較の元の comma 族への反映。
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

/-- 元の試験族への制限として得た、同じ実 comma 内の全族。 -/
def indArrowInterpolationOldFamily :=
  (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ indArrowInterpolationCommaFamily V

/-- 制限された元の実 comma 族の全余錐は、同じ再構成円柱の curry そのもの。 -/
lemma indArrowInterpolationOldFamily_uncurry :
    sliceOverUncurry (indArrowInterpolationOldFamily V ≫ diagramCommaSliceProjection κ D) =
      curry ((β_ (Δ[1] : SSet.{u + 1})
        (join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0])).hom ≫ r) ≫
          arrowDiagramUniverseRestriction (IndInfinity κ C) := by
  rw [indArrowInterpolationOldFamily, Category.assoc, sliceOverUncurry_precomp,
    indArrowInterpolationCommaFamily_uncurry, indArrowInterpolationLiftedCoconeMap_restrict]

/-- 元の試験族の slice 内の全余錐は、同じ元の標準全余錐そのもの。 -/
lemma diagramCommaSliceProjection_uncurry {T : SSet.{u + 1}} (f : T ⟶ diagramComma κ D) :
    sliceOverUncurry (f ≫ diagramCommaSliceProjection κ D) =
      joinMap f (𝟙 Δ[0]) ≫ (diagramCommaCocone κ D).val := by
  rw [sliceOverUncurry_precomp]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
