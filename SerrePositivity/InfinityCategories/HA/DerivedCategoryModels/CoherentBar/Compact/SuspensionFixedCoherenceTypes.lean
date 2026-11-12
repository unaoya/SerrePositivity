module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SphereClosureEdgeIsoAdapter

/-!
概要：固定 data の恒等・合成入力に要求する、端点固定の比較型を揃える。
方針：同じ実入力射の標準辺を区間写像空間の頂点として比較する。
規約：ε 圏の単位対象や、canonical data の恒等・合成に置き換えない。
使われ方：D-S の単位・合成の必要条件と、工程4の比較供給。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded KST.SConstruction KST.NonConnective
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)

/-- 固定恒等入力の実懸垂射と、実懸垂の恒等射との端点固定比較。 -/
abbrev DGSuspensionFixedUnitComparison
    (A : PerfDGInput.{u, max (u + 1) v} R) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalInputMap R κ hκ (𝟙 A))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (𝟙 (dgKappaSuspensionKInput R A
        (dgKappaUnconditionalStageProvider.{u, v} R κ hκ A).cone))))

/-- 固定合成入力と、二つの固定入力射の合成との端点固定比較。 -/
abbrev DGSuspensionFixedCompositionComparison
    {A B C : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) (g : B ⟶ C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalInputMap R κ hκ (f ≫ g))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalInputMap R κ hκ f ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalInputMap R κ hκ g)))

/-- 固定実入力射の恒等等号が得られた場合の、同じ固定端点比較。 -/
def dgSuspensionFixedUnitComparisonOfEq
    (A : PerfDGInput.{u, max (u + 1) v} R)
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalInputMap R κ hκ (𝟙 A) =
      𝟙 (dgKappaSuspensionKInput R A
        (dgKappaUnconditionalStageProvider.{u, v} R κ hκ A).cone)) :
    DGSuspensionFixedUnitComparison R κ hκ A := by
  unfold DGSuspensionFixedUnitComparison
  rw [h]

/-- 固定実入力射の合成等号が得られた場合の、同じ固定端点比較。 -/
def dgSuspensionFixedCompositionComparisonOfEq
    {A B C : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) (g : B ⟶ C)
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalInputMap R κ hκ (f ≫ g) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalInputMap R κ hκ f ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalInputMap R κ hκ g) :
    DGSuspensionFixedCompositionComparison R κ hκ f g := by
  unfold DGSuspensionFixedCompositionComparison
  rw [h]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
