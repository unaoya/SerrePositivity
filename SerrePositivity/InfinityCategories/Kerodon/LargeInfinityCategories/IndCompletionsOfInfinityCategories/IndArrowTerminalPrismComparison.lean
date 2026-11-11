module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndArrowTerminalPrismEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndArrowTerminalPrismBoundaryMap

/-!
概要：再構成した円柱と元の円柱を、元の C 図式と全区間 D を固定した fiber 内で比較する。
方針：実普遍族の両指定頂点と、同じ固定境界 fiber への全射で同型を移す。
規約：境界条件を忘れず元の全円柱を回収。使われ方：元の q の全変換の同型。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D}
  {H : T ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection D)}
  (W : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndArrowSlicePrism κ D q H)
local notation "R" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T Δ[0] ⊗ Δ[1]
local notation "a" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowOriginalFamily κ D q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C
local notation "d" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalToSmall ≫ D
local notation "r" => Iso.inv (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCoconeIso T) ≫
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion T ≫ W.val)

/-- 普遍円柱の頂点での全射の回収は、固定境界 fiber の包含後にも同じ頂点を与える。 -/
lemma indArrowTerminalPrismBoundaryMap_vertex_val
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowTerminalLiftFamily W) _⦋0⦌) (c : R ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
    (hv : (R ◁ SSet.yonedaEquiv.symm v) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowTerminalPrismFamily W = fst R Δ[0] ≫ c) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowTerminalPrismBoundaryMap W).app (Opposite.op ⦋0⦌) v).val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c := by
  change (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowTerminalPrismFamily W)).app (Opposite.op ⦋0⦌) v = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_comp]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, hv, SSet.yonedaEquiv_symm_zero,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 元の C 全図式と全 D を固定した、再構成円柱の頂点。 -/
def indArrowPrismReconstructedBoundaryVertex : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fixedArrowPrismBoundary a d) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowTerminalPrismBoundaryMap W).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowTerminalReconstructedVertex W)

/-- 元の C 全図式と全 D を固定した、元の円柱の頂点。 -/
def indArrowPrismOriginalBoundaryVertex : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fixedArrowPrismBoundary a d) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowTerminalPrismBoundaryMap W).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowTerminalOriginalVertex W)

/-- 両指定全境界を固定した同じ実 fiber 内で、元の全円柱を比較する同型。 -/
def indArrowPrismBoundaryIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (indArrowPrismReconstructedBoundaryVertex W)
      (indArrowPrismOriginalBoundaryVertex W) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowTerminalPrismVertexIso W) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowTerminalPrismBoundaryMap W)

/-- 最初の頂点の元の全写像は、同じ実 slice 円柱から再構成した円柱そのもの。 -/
lemma indArrowPrismReconstructedBoundaryVertex_val :
    (indArrowPrismReconstructedBoundaryVertex W).val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex r :=
  indArrowTerminalPrismBoundaryMap_vertex_val W _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowTerminalPrismFamily_reconstructed W)

/-- 次の頂点の元の全写像は、同じ元の q の全円柱そのもの。 -/
lemma indArrowPrismOriginalBoundaryVertex_val :
    (indArrowPrismOriginalBoundaryVertex W).val = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowNormalizedPrism κ D q) :=
  indArrowTerminalPrismBoundaryMap_vertex_val W _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowTerminalPrismFamily_original W)

/-- 固定境界の比較は、同じ元の全円柱の通常の関手同型としても読める。 -/
def indArrowReconstructionPrismIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso r (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowNormalizedPrism κ D q) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (indArrowPrismBoundaryIso W)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowPrismBoundaryRestriction T (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (snd (Δ[0] : SSet.{u + 1}) Δ[1] ≫ d)))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (indArrowPrismReconstructedBoundaryVertex W).val
    (indArrowPrismOriginalBoundaryVertex W).val at e
  simpa only [indArrowPrismReconstructedBoundaryVertex_val,
    indArrowPrismOriginalBoundaryVertex_val] using e

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
