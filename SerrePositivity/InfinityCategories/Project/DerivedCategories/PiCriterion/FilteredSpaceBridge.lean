module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.CoherentNativeCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.UniverseShape
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.RestrictionLeg
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredPosetNerve

/-!
概要：D が指定した全基点 π の元ごとの条件から、元の coherent 余錐の余極限性を導く。
方針：底だけを値の宇宙に持ち上げ、同じ脚・transition の native 判定を適用する。
規約：D の公開構造を直接消費し、元の図式と余錐を結論に保つ。
使われ方：D-8 c2 の DGBarCompactFilteredSpacePiBridge の供給。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

/-- D の指定宇宙・元の脚・元の transition に対する、全基点 π による余極限判定。 -/
theorem dgBarCompactFilteredSpacePiBridge (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactFilteredSpacePiBridge.{u, v} κ := by
  intro I _ _ F c hd
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (nerve I) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered I
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity (nerve I) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_of_isKappaFiltered (Fact.out : κ.IsRegular).aleph0_le (nerve I)
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity ((SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isFilteredInfinity_ulift (nerve I)
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.liftedBaseDiagram.{u, max (u + 1) v} F
  let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G := c.restrict (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.liftedBaseShapeIso.{u, max (u + 1) v} (nerve I)).hom
  let r : I → ((SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I)) _⦋0⦌ :=
    fun i ↦ ULift.up (nerveEquiv.symm i)
  have hr : Function.Surjective r := by
    rintro ⟨b⟩
    exact ⟨nerveEquiv b, congrArg ULift.up (nerveEquiv.symm_apply_apply b)⟩
  let e : ∀ {i j : I}, i ≤ j →
      ((SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I)).Edge (r i) (r j) :=
    fun hij ↦ SSet.Edge.ofTruncated
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge (X := nerve I) (CategoryTheory.nerve.edgeMk (homOfLE hij)).toTruncated)
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.isColimitCone_iff_liftedBase_restrict.{u, max (u + 1) v} c).mpr
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.isColimitCone_of_coherent_spacePiData G d r e hr
  dsimp only [G, d, r, e, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.liftedBaseDiagram]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.coconeTransportLeg_restrict]
  exact hd

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
