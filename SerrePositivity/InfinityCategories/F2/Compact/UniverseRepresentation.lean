module

public import SerrePositivity.InfinityCategories.F2.Compact.UniverseUnstraightening
public import SerrePositivity.InfinityCategories.F1.LeftFibrationFiberReflection

/-!
概要：同じ空間の宇宙変更は、元の全空間の宇宙持ち上げを実際に表現する。
方針：構成した底上の比較を持ち上げ、厳密な縮小同型と全 fiber の反映を合成。
規約：比較・図式・射影を同時に固定する。存在を未証明の入力に置かない。
使われ方：元の余錐全体の相対表現を、図式と頂点へ同時に制限する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の全空間の持ち上げから、同じ宇宙変更の実際の大きい全空間への一つの比較。 -/
def spaceUniverseTotalComparison {B : SSet.{u + 1}} [Quasicategory B]
    (F : B ⟶ SpaceInfinity.{u}) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (leftUnstraightening F) ⟶
      leftUnstraightening
        ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ spaceUniverseDiagram.{u}) :=
  (SSet.uliftFunctor.{u + 2, u + 1}).map (spaceUniverseUnstraighteningComparison F) ≫
    (smallLeftUnstraighteningIso _).hom

/-- 大きい全空間の実際の比較は、同じ持ち上げた元の射影を厳密に保つ。 -/
lemma spaceUniverseTotalComparison_projection {B : SSet.{u + 1}} [Quasicategory B]
    (F : B ⟶ SpaceInfinity.{u}) :
    spaceUniverseTotalComparison F ≫ leftUnstraighteningProjection
      ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ spaceUniverseDiagram.{u}) =
      (SSet.uliftFunctor.{u + 2, u + 1}).map (leftUnstraighteningProjection F) := by
  rw [spaceUniverseTotalComparison, Category.assoc, smallLeftUnstraighteningIso_projection,
    ← Functor.map_comp, spaceUniverseUnstraighteningComparison_projection]

/-- 同じ大きい全空間の比較自身は、全 quasicategory 標的への前合成同値。 -/
lemma spaceUniverseTotalComparison_isPrecompositionEquivalence
    {B : SSet.{u + 1}} [Quasicategory B] (F : B ⟶ SpaceInfinity.{u}) :
    IsPrecompositionEquivalence (spaceUniverseTotalComparison F) := by
  have : Quasicategory (leftUnstraightening F) :=
    quasicategory_of_innerFibration (leftUnstraighteningProjection F)
  have h :=
    (spaceUniverseUnstraighteningComparison_isPrecompositionEquivalence F).isQCatEquivalence
  have hU := IsQCatEquivalence.ulift.{u + 1, u + 2} h
  exact hU.isPrecompositionEquivalence.comp
    (isPrecompositionEquivalence_of_iso (smallLeftUnstraighteningIso _))

/-- 指定した同じ宇宙変更図式は、元の全空間の持ち上げを全 fiber で実際に表現する。 -/
def spaceUniverseTransportRepresentation {B : SSet.{u + 1}} [Quasicategory B]
    (F : B ⟶ SpaceInfinity.{u}) :
    LeftTransportRepresentation
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (leftUnstraighteningProjection F)) where
  diagram := (SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ spaceUniverseDiagram.{u}
  comparison := spaceUniverseTotalComparison F
  over_base := spaceUniverseTotalComparison_projection F
  fiber_equivalence := vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence _ _
    (spaceUniverseTotalComparison F) (spaceUniverseTotalComparison_projection F)
    (spaceUniverseTotalComparison_isPrecompositionEquivalence F)

end SerrePositivity.InfinityCategories.F2.Compact
