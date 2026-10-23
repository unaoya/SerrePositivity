module
public import SerrePositivity.KST.Fibration.CocartesianKanDiagram
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StrictTransportInclusion
public import SerrePositivity.InfinityCategories.F1.LeftFibrationInitialEvaluation
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningCandidate
public import SerrePositivity.InfinityCategories.F1.KanDiagramNaturalTransformation

/-! # left fibration の同じ strict Kan 図式と分類候補の比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- Kan 値図式の元の各値を、同じ関手的 Kan 置換へ自然に含める。 -/
def kanDiagramCompletionUnit {I : Type u} [Category.{u} I] (F : I ⥤ KanObject.{u}) :
    F ⋙ kanObjectForget ⟶ F ⋙ kanObjectForget ⋙ strictKanCompletion ⋙ kanObjectForget where
  app c := F2.continuousKanReplacementUnit.app (F.obj c).obj
  naturality {_c _d} f := F2.continuousKanReplacementUnit.naturality (F.map f)

/-- 元の図式とその同じ Kan 置換は、全 coherent 図式として自然同型。 -/
def kanDiagramCompletionIso {I : Type u} [Category.{u} I] (F : I ⥤ KanObject.{u}) :
    FunctorIso (kanDiagramCoherentNerve F)
      (kanDiagramCoherentNerve (F ⋙ kanObjectForget ⋙ strictKanCompletion)) := by
  apply kanDiagramFunctorIsoOfPointwise
    (F := ⟨F, trivial⟩) (G := ⟨F ⋙ kanObjectForget ⋙ strictKanCompletion, trivial⟩)
    (kanDiagramCompletionUnit F)
  intro c
  apply isQCatEquivalence_of_anodyneQ_isIso
  exact SSet.anodyneExtensions.Q_inverts _ (F2.continuousKanReplacementUnit_anodyne _)

/-- 元の cocartesian section の包含を、同じ Kan 置換後の図式間の自然変換にする。 -/
def leftCocartesianKanComparison {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [LeftFibration p] :
    cocartesianKanDiagram p ⟶ leftStrictTransportFunctor p ⋙ kanObjectForget ⋙
      strictKanCompletion :=
  Functor.whiskerRight (cocartesianStrictTransportInclusion p) strictKanCompletion

/-- 同じ left fibration の全 cocartesian section と全 section の coherent 図式は同型。 -/
def leftCocartesianKanComparisonIso {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [LeftFibration p] :
    FunctorIso (cocartesianKanCoherentDiagram p) (leftStraighteningCandidate p) := by
  have e := kanDiagramFunctorIsoOfPointwise
    (F := ⟨cocartesianKanDiagram p, trivial⟩)
    (G := ⟨leftStrictTransportFunctor p ⋙ kanObjectForget ⋙ strictKanCompletion, trivial⟩)
    (Functor.whiskerRight (leftCocartesianKanComparison p) kanObjectForget) (fun c => by
      have := kanCocartesianSectionsι_isIso_of_leftFibration p (nerveMap (Under.forget c))
      apply strictKanCompletion_map_isQCatEquivalence
      change IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
        (kanCocartesianSectionsι p (nerveMap (Under.forget c))))
      infer_instance)
  exact e ≪≫ (kanDiagramCompletionIso (leftStrictTransportFunctor p)).symm

end SerrePositivity.KST.Fibration
