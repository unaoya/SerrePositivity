module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.OrdinaryComparisonPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexLocalizationData
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：標準単体の初頂点切断の、辺を反転する関手での coherent な比較。
方針：標準切断の自然変換を prism に実現し、その全ての縦辺を反転する。
規約：反転条件だけを使い、局所化の普遍性は仮定しない。
使われ方：単体圏から元の底への降下の局所的な比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 初頂点で制限して切断へ戻す操作から恒等射への、全次数の比較。 -/
def transportStandardSectionHomotopy (n : ℕ) :
    SSet.Homotopy
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardFirstVertex.{u} n) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSection n)) (𝟙 _) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.ordinaryComparisonHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSectionComparison n)

/-- 指定した関手に標準切断の比較を適用する実際のホモトピー。 -/
def transportStandardInvertingHomotopy (n : ℕ) {E : SSet.{u}}
    (U : nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (Δ[n] : SSet.{u})) ⟶ E) :
    SSet.Homotopy
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardFirstVertex n) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSection n) ≫ U) U :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (transportStandardSectionHomotopy n) U

/-- 始点を保つ射を反転する関手では、標準切断の比較は全体として可逆。 -/
lemma transportStandardInvertingHomotopy_isInvertible (n : ℕ) {E : SSet.{u}}
    [Quasicategory E]
    (U : nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (Δ[n] : SSet.{u})) ⟶ E)
    (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges U (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n])) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (transportStandardInvertingHomotopy n U)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise
  intro x
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (x.obj 0) = x := ComposableArrows.ext₀ rfl
  rw [← hx]
  have h := hU (by exact ⟨_, _, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSectionComparison n).app (x.obj 0),
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSectionComparison_preservesFirst _, rfl⟩)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (transportStandardInvertingHomotopy n U)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (x.obj 0))).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (nerve.edgeMk
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSectionComparison n).app (x.obj 0))).edge).map
        ((truncation 2).map U)).edge from ?_)).mpr h
  exact congrArg (fun s ↦ U.app (Opposite.op ⦋1⦌) s)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.ordinaryComparisonHomotopy_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSectionComparison n) (x.obj 0))

/-- 辺を反転する関手を初頂点に制限して戻した関手との coherent な同型。 -/
def transportStandardInvertingComparisonIso (n : ℕ) {E : SSet.{u}}
    [Quasicategory E]
    (U : nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (Δ[n] : SSet.{u})) ⟶ E)
    (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges U (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n])) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardFirstVertex n) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSection n) ≫ U) U := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (transportStandardInvertingHomotopy n U)
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk e) :=
    transportStandardInvertingHomotopy_isInvertible n U hU
  exact asIso (SSet.Truncated.HomotopyCategory.homMk e)

/-- 標準切断に沿う制限で、元の標準単体上の実際の関手を得る。 -/
def transportStandardInvertingDescent (n : ℕ) {E : SSet.{u}}
    (U : nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (Δ[n] : SSet.{u})) ⟶ E) : Δ[n] ⟶ E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardFirstVertexSection n ≫ U

/-- 元の標準単体上の関手は、引き戻してから降ろすと厳密に回収される。 -/
lemma transportStandardInvertingDescent_recover (n : ℕ) {E : SSet.{u}} (V : Δ[n] ⟶ E) :
    transportStandardInvertingDescent n (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap Δ[n] ≫ V) = V := by
  dsimp only [transportStandardInvertingDescent]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardFirstVertexSection_comp, Category.id_comp]

/-- 降下した関手の引き戻しと、元の辺を反転する関手との coherent な同型。 -/
def transportStandardInvertingDescentIso (n : ℕ) {E : SSet.{u}} [Quasicategory E]
    (U : nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (Δ[n] : SSet.{u})) ⟶ E)
    (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges U (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges Δ[n])) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap Δ[n] ≫
      transportStandardInvertingDescent n U) U := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap Δ[n] ≫ transportStandardInvertingDescent n U =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardFirstVertex n) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardSection n) ≫ U := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardFirstVertex_nerve]
    dsimp only [transportStandardInvertingDescent, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportStandardFirstVertexSection]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]
  exact transportStandardInvertingComparisonIso n U hU

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
