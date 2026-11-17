module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramModelLocalization
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelRightFrameComparison

/-!
概要：元のstrict複体図式の実right frameを、同じ指定局所化のpinched Homへ比較する。
方針：同じ関手的分解・宇宙表示・局所化を、既存の全モデル圏のhammock比較へ渡す。
規約：源のcofibrancyはこの中間比較だけの条件。最終的な任意頂点の比較は別に構成する。
使われ方：HTT 4.2.4.4の加群版の局所化側の写像空間。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory _root_.HomotopicalAlgebra SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance isw1StrictDiagramRightFrameComparisonLocal1 : CategoryTheory.Limits.HasCoproducts.{u} (DifferentialGraded.Complex A) :=
  fun _ => HomologicalComplex.instHasColimitsOfShape
local instance isw1StrictDiagramRightFrameComparisonLocal2 : CategoryTheory.Limits.HasCoproducts.{0} (DifferentialGraded.Complex A) :=
  fun _ => HomologicalComplex.instHasColimitsOfShape
local instance isw1StrictDiagramRightFrameComparisonLocal3 : CategoryTheory.Limits.HasInitial (StrictComplexDiagram A d) :=
  (CategoryTheory.Limits.isZero_zero (StrictComplexDiagram A d)).isInitial.hasInitial
local instance isw1StrictDiagramRightFrameComparisonLocal4 : ModelCategory (StrictComplexDiagram A d) := strictDiagramReedyModelCategory A d
local instance isw1StrictDiagramRightFrameComparisonLocal5 : CategoryTheory.Limits.HasTerminal (StrictComplexDiagram A d) :=
  (CategoryTheory.Limits.isZero_zero (StrictComplexDiagram A d)).isTerminal.hasTerminal
local instance isw1StrictDiagramRightFrameComparisonLocal6 : (cofibrations (StrictComplexDiagram A d)).HasFunctorialFactorization
    (trivialFibrations (StrictComplexDiagram A d)) :=
  strictDiagramReedy_cof_hasFunctorialFactorization A d

/-- Hovey §5.2の同じ第二関手的分解から取るright frameの全族。 -/
def strictDiagramRightFrameFamily :
    Reedy.CofibrantResolutionFamily (C := (StrictComplexDiagram A d)ᵒᵖ) Reedy.simplex :=
  rightFrameFamilyOfFactorization (strictDiagramFibFactorizationData A d)

/-- 元の全標的で自然な、同じright frameへの実Hom。 -/
def strictDiagramRightFrameMapping (X : StrictComplexDiagram A d) :
    StrictComplexDiagram A d ⥤ SSet.{u} :=
  rightFrameHom (strictDiagramRightFrameFamily A d) X

local instance isw1StrictDiagramRightFrameComparisonLocal7 (X Y : StrictComplexDiagram A d) [IsCofibrant X] :
    SSet.KanComplex ((strictDiagramRightFrameMapping A d X).obj Y) :=
  rightFrameHom_kanComplex (strictDiagramRightFrameFamily A d) X Y

/-- 実right frameと元の指定局所化の同じ両端のpinched Homの全同値。 -/
def strictDiagramRightFramePinchedEquivalence
    (X Y : StrictComplexDiagram A d) [IsCofibrant X] :
    QCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).obj ((strictDiagramRightFrameMapping A d X).obj Y))
      (pinchedHom (X := StrictDiagramInfinity A d)
        ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X))
        ((strictDiagramLocalization A d).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ Y))) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelRightFramePinchedEquivalence
    (strictDiagramRightFrameFamily A d) (strictDiagramModelLocalization A d)
    (strictDiagramModelLocalization_isLocalization A d) X Y

/-- 同じ局所化側の比較射は単体的ホモトピー同値である。 -/
lemma strictDiagramRightFramePinchedEquivalence_homotopyEquivalence
    (X Y : StrictComplexDiagram A d) [IsCofibrant X] :
    IsSimplicialHomotopyEquivalence (strictDiagramRightFramePinchedEquivalence A d X Y).hom :=
  (strictDiagramRightFramePinchedEquivalence A d X Y).isQCatEquivalence.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
