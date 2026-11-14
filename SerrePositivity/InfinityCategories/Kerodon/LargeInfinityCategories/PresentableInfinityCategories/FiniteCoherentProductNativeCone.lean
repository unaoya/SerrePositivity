module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.EdgeApexPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SpecifiedApexConeRestrictions
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CoherentFilteredTotalDetection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.SpecifiedApexLimitConeTransport
public import SerrePositivity.InfinityCategories.HTT.Section3_3_4.CoherentTotalObject
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteCoherentProductKanComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.FiniteCoherentProductTotalMap
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FiniteKanProductComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FiniteKanProductNative
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.NonemptyFiniteSSetProduct
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：元の有限 coherent 積図式の余極限 Kan 模型を頂点とする、native な全有限積錐。
方針：元の有限 coherent 積比較の同じ辺で元の反復積の全錐を輸送する。
規約：同じ頂点辺と、全時刻で元の底図式を固定する全錐円柱を保持する。
使われ方：P_Σ の sifted 余極限閉性で使う全有限非空積の比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable (n : ℕ) {B : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B]
  (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))

/-- 元の有限積比較を、元の Kan 対象間の指定射に束ねる。 -/
def finiteCoherentTotalComparisonKanMap :
    _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) ⟶
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n (fun i ↦ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject (F i)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteCoherentProductTotalKanComparison n F

/-- 元の有限積比較の coherent な辺そのものを持つ頂点円柱。 -/
def finiteCoherentTotalComparisonApexPrism :
    (Δ[1] : SSet.{u + 1}) ⊗ (Δ[0] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (finiteCoherentTotalComparisonKanMap n F))

/-- 元の全空間の有限積比較による、頂点指定の全極限錐の輸送。 -/
def finiteSiftedCoherentProductNativeConeTransport : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.SpecifiedApexLimitConeTransport
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone n (fun i ↦ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject (F i)))
    (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F))))
    (finiteCoherentTotalComparisonApexPrism n F) := by
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n
      (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan (F i))) :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct_kanComplex _ _ (fun _ ↦ inferInstance)
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.specifiedApexLimitConeTransport _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone_isLimit _ _) _ _
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism_zero _) (by
      unfold finiteCoherentTotalComparisonApexPrism
      rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism_one]
      apply SSet.yonedaEquiv.injective
      change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _ = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone n
        (fun i ↦ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject (F i))).vertex
      exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone_vertex _ _).symm)
    (fun x ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism_vertical_isInvertible _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteCoherentProductTotalKanComparison_homotopyEquivalence n F).isQCatEquivalence) x)

/-- 元の有限 coherent 積図式の余極限 Kan 模型を頂点とする native な全有限積錐。 -/
def finiteSiftedCoherentProductNativeCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n (fun i ↦ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject (F i)))) :=
  (finiteSiftedCoherentProductNativeConeTransport n F).cone

/-- 元の全空間 Kan 模型を頂点とする全錐は、実際の native な有限積錐。 -/
lemma finiteSiftedCoherentProductNativeCone_isLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (finiteSiftedCoherentProductNativeCone n F) :=
  (finiteSiftedCoherentProductNativeConeTransport n F).isLimit

/-- 輸送した native 全錐の頂点は、元の有限 coherent 積図式の余極限模型と厳密に一致。 -/
lemma finiteSiftedCoherentProductNativeCone_vertex :
    (finiteSiftedCoherentProductNativeCone n F).vertex =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F)) := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ (finiteSiftedCoherentProductNativeCone n F).val) = _
  dsimp only [finiteSiftedCoherentProductNativeCone]
  rw [(finiteSiftedCoherentProductNativeConeTransport n F).apex_eq, Equiv.apply_symm_apply]

/-- 元の反復積錐への、同じ比較辺を頂点辺とする全錐ホモトピー。 -/
def finiteSiftedCoherentProductNativeConeHomotopy :
    SSet.Homotopy (finiteSiftedCoherentProductNativeCone n F).val
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone n (fun i ↦ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject (F i))).val :=
  (finiteSiftedCoherentProductNativeConeTransport n F).homotopy

/-- 全錐円柱の頂点制限は元の有限積比較の同じ円柱。 -/
lemma finiteSiftedCoherentProductNativeConeHomotopy_apex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (finiteSiftedCoherentProductNativeConeHomotopy n F).h =
      (β_ (Δ[0] : SSet.{u + 1}) (Δ[1] : SSet.{u + 1})).hom ≫
        finiteCoherentTotalComparisonApexPrism n F :=
  (finiteSiftedCoherentProductNativeConeTransport n F).apex

/-- 全錐円柱の底制限は全時刻で元の全空間の図式そのもの。 -/
lemma finiteSiftedCoherentProductNativeConeHomotopy_diagram :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (finiteSiftedCoherentProductNativeConeHomotopy n F).h =
      fst _ (Δ[1] : SSet.{u + 1}) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n (fun i ↦ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject (F i))) :=
  (finiteSiftedCoherentProductNativeConeTransport n F).diagram

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
