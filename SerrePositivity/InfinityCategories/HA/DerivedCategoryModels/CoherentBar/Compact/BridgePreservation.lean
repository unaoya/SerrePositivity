module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.FilteredSpaceBridgeInput
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationGeneratorClosure
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ProjectiveBarNativeCocone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.UnconditionalCovers
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitReindex
/-!
概要：元ごとの π 判定の橋を全 native 余極限保存と K-7 入力へ接続する。
方針：実 bar 余錐を一重の添字持ち上げへ戻し、同じ全余錐の同型と poset 帰着を使う。
規約：π 条件の導出はこの中間入口では明示入力。strict 比較で保存を代用しない。
使われ方：評価ホモロジーから π 条件を証明した後、橋だけを残す接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial

/-- 添字の一重・二重の持ち上げを、元の単体を変えず比較する。 -/
def dgBarCompactIndexLiftIso (I : SSet.{u}) :
    (SSet.uliftFunctor.{max (u + 1) v + 1, u}).obj I ≅
      (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
        ((SSet.uliftFunctor.{max (u + 1) v, u}).obj I) where
  hom := { app n := ↾fun s => ULift.up (ULift.up s.down)
           naturality := by intros; rfl }
  inv := { app n := ↾fun s => ULift.up s.down.down
           naturality := by intros; rfl }
  hom_inv_id := by ext n s; rfl
  inv_hom_id := by ext n s; rfl

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : Type u} [PartialOrder I]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D)
  (x : D)

def dgBarCompactEvaluationPosetDiagram :
    (SSet.uliftFunctor.{max (u + 1) v + 1, u}).obj (nerve I) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v} :=
  (dgBarCompactIndexLiftIso.{u, v} (nerve I)).hom ≫
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map G ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x

def dgBarCompactEvaluationPosetCocone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (dgBarCompactEvaluationPosetDiagram R D G x) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarNativeCocone R D G))).restrict
      (dgBarCompactIndexLiftIso.{u, v} (nerve I)).hom

variable {κ : Cardinal.{u}} [Fact κ.IsRegular]

lemma dgBarCompactEvaluation_preserves_of_bridge_and_posetPi
    (bridge : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactFilteredSpacePiBridge.{u, v} κ)
    (hPi : ∀ (I : Type u) [PartialOrder I] [IsCardinalFiltered I κ]
      (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I) ⟶
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D),
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactFilteredSpacePiData (dgBarCompactEvaluationPosetDiagram R D G x)
        (dgBarCompactEvaluationPosetCocone R D G x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, max (u + 1) v} κ
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Compact.preservesKappaFilteredColimits_of_poset
  intro J hJ hFiltered H c hc
  let d := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarNativeCocone R D H
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarNativeCocone_isColimit R D H
  let E := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone E (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift d)) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso _
      (dgBarCompactIndexLiftIso.{u, v} (nerve J)).hom).mpr
    exact bridge J (dgBarCompactEvaluationPosetDiagram R D H x)
      (dgBarCompactEvaluationPosetCocone R D H x) (hPi J H)
  have hd' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift d) := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isColimitCone_iff_ulift d).mp hd
  have hc' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c) := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isColimitCone_iff_ulift c).mp hc
  exact he.of_functorIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFunctorIsoOfVertexIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift d)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso _ _ hd' hc')).postcomp E)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
