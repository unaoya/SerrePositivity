module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SphereClosureQuotientEdge

/-!
概要：最終懸垂作用の辺と native 商作用の辺の比較を、採用 edgeIso の型へ接続する。
方針：端点固定の指定同型を、正本入力辺への既存の同型と合成する。
規約：map の構成やその辺の比較の存在は仮定から結論しない。
使われ方：D-S の map 到着後の工程4。square と square_at は別工程。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded KST.SConstruction KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)
variable
  (m : dgKInputInfinity.{u, max (u + 1) v} R ⟶ dgKInputInfinity.{u, max (u + 1) v} R)
  (hv : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
    m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaSuspensionKInput R A
        (dgKappaUnconditionalStageProvider.{u, v} R κ hκ A).cone))
  {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B)

/-- 最終辺から商作用辺への指定同型を、端点固定の正本 data の edgeIso に接続する。 -/
def dgSuspensionEdgeIsoOfQuotientComparison
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSuspensionMappedEdge R
      (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) m hv f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionQuotientNativeEdge R κ hκ f))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSuspensionMappedEdge R
      (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) m hv f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (dgKappaSuspensionInputMap R A B
          (dgKappaUnconditionalStageProvider.{u, v} R κ hκ A).cone
          (dgKappaUnconditionalStageProvider.{u, v} R κ hκ B).cone
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ f)))) :=
  h.trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionQuotientNativeEdgeIso R κ hκ f)

/-- 最終辺と商作用辺の厳密な一単体等号から、同じ端点固定 edgeIso を得る。 -/
def dgSuspensionEdgeIsoOfQuotientEdgeEq
    (h : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSuspensionMappedEdge R
      (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) m hv f).edge =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionQuotientNativeEdge R κ hκ f).edge) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSuspensionMappedEdge R
      (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) m hv f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (dgKappaSuspensionInputMap R A B
          (dgKappaUnconditionalStageProvider.{u, v} R κ hκ A).cone
          (dgKappaUnconditionalStageProvider.{u, v} R κ hκ B).cone
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ f)))) := by
  have he : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSuspensionMappedEdge R
      (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) m hv f =
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionQuotientNativeEdge R κ hκ f :=
    SSet.Edge.ext h
  rw [he]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgSuspensionQuotientNativeEdgeIso R κ hκ f

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
