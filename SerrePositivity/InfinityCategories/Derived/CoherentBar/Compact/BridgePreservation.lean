module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.FilteredSpaceBridgeInput
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationGeneratorClosure
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ProjectiveBarNativeCocone
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.UnconditionalCovers
public import SerrePositivity.InfinityCategories.Core.ColimitReindex
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
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

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : Type u} [PartialOrder I]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I) ⟶ dgProjectiveModuleNerve R D)
  (x : D)

def dgBarCompactEvaluationPosetDiagram :
    (SSet.uliftFunctor.{max (u + 1) v + 1, u}).obj (nerve I) ⟶
      SpaceInfinity.{max (u + 1) v} :=
  (dgBarCompactIndexLiftIso.{u, v} (nerve I)).hom ≫
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map G ≫
      dgBarCompactProjectiveEvaluationSpaceInfinity R D x

def dgBarCompactEvaluationPosetCocone :
    JoinCocone (dgBarCompactEvaluationPosetDiagram R D G x) :=
  (mapJoinCocone (dgBarCompactProjectiveEvaluationSpaceInfinity R D x)
    (JoinCocone.ulift (dgProjectiveBarNativeCocone R D G))).restrict
      (dgBarCompactIndexLiftIso.{u, v} (nerve I)).hom

variable {κ : Cardinal.{u}} [Fact κ.IsRegular]

lemma dgBarCompactEvaluation_preserves_of_bridge_and_posetPi
    (bridge : DGBarCompactFilteredSpacePiBridge.{u, v} κ)
    (hPi : ∀ (I : Type u) [PartialOrder I] [IsCardinalFiltered I κ]
      (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I) ⟶
        dgProjectiveModuleNerve R D),
      DGBarCompactFilteredSpacePiData (dgBarCompactEvaluationPosetDiagram R D G x)
        (dgBarCompactEvaluationPosetCocone R D G x)) :
    F2.Compact.PreservesKappaFilteredColimits.{u, max (u + 1) v} κ
      (dgBarCompactProjectiveEvaluationSpaceInfinity R D x) := by
  apply F2.Ind.Compact.preservesKappaFilteredColimits_of_poset
  intro J hJ hFiltered H c hc
  let d := dgProjectiveBarNativeCocone R D H
  have hd : IsColimitCone d := dgProjectiveBarNativeCocone_isColimit R D H
  let E := dgBarCompactProjectiveEvaluationSpaceInfinity R D x
  have he : IsColimitCone (mapJoinCocone E (JoinCocone.ulift d)) := by
    apply (isColimitCone_iff_restrict_of_isIso _
      (dgBarCompactIndexLiftIso.{u, v} (nerve J)).hom).mpr
    exact bridge J (dgBarCompactEvaluationPosetDiagram R D H x)
      (dgBarCompactEvaluationPosetCocone R D H x) (hPi J H)
  have hd' : IsColimitCone (JoinCocone.ulift d) := (isColimitCone_iff_ulift d).mp hd
  have hc' : IsColimitCone (JoinCocone.ulift c) := (isColimitCone_iff_ulift c).mp hc
  exact he.of_functorIso ((coconeFunctorIsoOfVertexIso (JoinCocone.ulift d)
    (JoinCocone.ulift c) (colimitConeIso _ _ hd' hc')).postcomp E)

end SerrePositivity.InfinityCategories
