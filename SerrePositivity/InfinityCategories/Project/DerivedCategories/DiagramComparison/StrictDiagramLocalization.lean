module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictComplexDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneralLocalization

/-!
概要：strict複体図式をobjectwise擬同型で∞局所化した、同じ宇宙の準圏模型。
方針：既存の任意辺集合の局所化を、元のnerveの指定辺集合に適用する。
規約：指定局所化写像と全関手圏の普遍性を保持し、評価同値はまだ主張しない。
使われ方：3b-3 R1、HTT 4.2.4.4の加群版の源の構成。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)

/-- 元のstrict図式のobjectwise擬同型による、同じ宇宙の∞局所化模型。 -/
def StrictDiagramInfinity : SSet.{u + 1} :=
  edgeLocalization (strictComplexDiagramNerve A d) (strictDiagramWeakEdges A d)

instance strictDiagramInfinity_quasicategory : Quasicategory (StrictDiagramInfinity A d) :=
  edgeLocalization_quasicategory _ _

/-- 元の全strict図式のnerveからの指定局所化写像。 -/
def strictDiagramLocalization : strictComplexDiagramNerve A d ⟶ StrictDiagramInfinity A d :=
  edgeLocalizationMap _ _

/-- 指定写像は元のobjectwise擬同型辺に関する∞局所化である。 -/
theorem strictDiagramLocalization_isLocalization :
    IsLocalization (strictDiagramLocalization A d) (strictDiagramWeakEdges A d) :=
  edgeLocalization_isLocalization _ _

/-- 指定局所化写像は、元のobjectwise擬同型辺を可逆にする。 -/
lemma strictDiagramLocalization_inverts :
    InvertsEdges (strictDiagramLocalization A d) (strictDiagramWeakEdges A d) :=
  edgeLocalization_inverts _ _

/-- 任意の同宇宙の準圏への全関手圏に対する、指定局所化の普遍性。 -/
theorem strictDiagramLocalization_universal (E : SSet.{u + 1}) [Quasicategory E] :
    IsQCatEquivalence (localizationPrecomposition (strictDiagramLocalization A d)
      (strictDiagramWeakEdges A d) (strictDiagramLocalization_inverts A d) E) :=
  edgeLocalization_universal _ _ E

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
