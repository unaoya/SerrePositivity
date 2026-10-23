module

public import SerrePositivity.InfinityCategories.F2.Compact.UniverseUnstraightening
public import SerrePositivity.InfinityCategories.F2.Compact.ClassificationTransport
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence

/-!
概要：元の left fibration の全分類図式は、指定された空間の宇宙変更と全自然同型。
方針：元の復元比較を持ち上げ、同じ全空間の縮小同型を合成して分類する。
規約：同じ元の射影と指定された宇宙変更を保持。各 fiber の比較で代用しない。
使われ方：前層の宇宙変更が元の全 Yoneda 図式を保つことの比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Compact
variable {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]

/-- 元の全空間の持ち上げを、同じ元の分類図式の全 unstraightening へ比較する。 -/
def leftClassificationUniverseComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj E ⟶
      leftUnstraightening (leftStraighteningInfinityDiagram p) :=
  (SSet.uliftFunctor.{u + 1, u}).map (leftStraighteningInfinityReconstruction p) ≫
    (smallLeftUnstraighteningIso _).hom

/-- 同じ元の全空間比較は、持ち上げた元の射影を厳密に保持する。 -/
lemma leftClassificationUniverseComparison_projection :
    leftClassificationUniverseComparison p ≫
      leftUnstraighteningProjection (leftStraighteningInfinityDiagram p) =
    (SSet.uliftFunctor.{u + 1, u}).map p := by
  rw [leftClassificationUniverseComparison, Category.assoc,
    smallLeftUnstraighteningIso_projection, ← Functor.map_comp,
    leftStraighteningInfinityReconstruction_projection]

/-- 元の全空間比較自身は、全 quasicategory 標的への前合成同値。 -/
lemma leftClassificationUniverseComparison_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (leftClassificationUniverseComparison p) := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  have h : IsQCatEquivalence (leftStraighteningInfinityReconstruction p) :=
    (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p).isQCatEquivalence
  exact (IsQCatEquivalence.ulift.{u, u + 1} h).isPrecompositionEquivalence.comp
    (isPrecompositionEquivalence_of_iso (smallLeftUnstraighteningIso _))

/-- 元の left fibration の持ち上げの分類は、元の分類の指定宇宙変更と全自然同型。 -/
def leftStraighteningInfinityDiagram_uliftIso :
    FunctorIso (leftStraighteningInfinityDiagram ((SSet.uliftFunctor.{u + 1, u}).map p))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (leftStraighteningInfinityDiagram p) ≫
        spaceUniverseDiagram.{u}) :=
  leftClassification_of_precompositionEquivalence _ _
    (leftClassificationUniverseComparison p) (leftClassificationUniverseComparison_projection p)
    (leftClassificationUniverseComparison_isPrecompositionEquivalence p) ≪≫
      spaceUniverseUnstraightening_classificationIso (leftStraighteningInfinityDiagram p)

end SerrePositivity.InfinityCategories.HomotopyLimits
