module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.OrdinaryComparisonPrism
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexLocalizationData
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-!
概要：標準単体の初頂点切断の、辺を反転する関手での coherent な比較。
方針：標準切断の自然変換を prism に実現し、その全ての縦辺を反転する。
規約：反転条件だけを使い、局所化の普遍性は仮定しない。
使われ方：単体圏から元の底への降下の局所的な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 初頂点で制限して切断へ戻す操作から恒等射への、全次数の比較。 -/
def transportStandardSectionHomotopy (n : ℕ) :
    SSet.Homotopy
      (nerveMap (transportStandardFirstVertex.{u} n) ≫
        nerveMap (transportStandardSection n)) (𝟙 _) :=
  ordinaryComparisonHomotopy (transportStandardSectionComparison n)

/-- 指定した関手に標準切断の比較を適用する実際のホモトピー。 -/
def transportStandardInvertingHomotopy (n : ℕ) {E : SSet.{u}}
    (U : nerve (TransportSimplexCategory (Δ[n] : SSet.{u})) ⟶ E) :
    SSet.Homotopy
      (nerveMap (transportStandardFirstVertex n) ≫
        nerveMap (transportStandardSection n) ≫ U) U :=
  functorHomotopyPostcomp (transportStandardSectionHomotopy n) U

/-- 始点を保つ射を反転する関手では、標準切断の比較は全体として可逆。 -/
lemma transportStandardInvertingHomotopy_isInvertible (n : ℕ) {E : SSet.{u}}
    [Quasicategory E]
    (U : nerve (TransportSimplexCategory (Δ[n] : SSet.{u})) ⟶ E)
    (hU : InvertsEdges U (transportSimplexInitialEdges Δ[n])) :
    IsInvertibleEdge (functorEdgeOfSimplicialHomotopy
      (transportStandardInvertingHomotopy n U)) := by
  apply functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise
  intro x
  have hx : nerveVertex (x.obj 0) = x := ComposableArrows.ext₀ rfl
  rw [← hx]
  have h := hU (by exact ⟨_, _, (transportStandardSectionComparison n).app (x.obj 0),
    transportStandardSectionComparison_preservesFirst _, rfl⟩)
  apply (isInvertibleEdge_congr (show
    (simplicialHomotopyVertexEdge (transportStandardInvertingHomotopy n U)
      (nerveVertex (x.obj 0))).edge =
      ((edgeOfSimplex (nerve.edgeMk
        ((transportStandardSectionComparison n).app (x.obj 0))).edge).map
        ((truncation 2).map U)).edge from ?_)).mpr h
  exact congrArg (fun s ↦ U.app (Opposite.op ⦋1⦌) s)
    (ordinaryComparisonHomotopy_vertex (transportStandardSectionComparison n) (x.obj 0))

/-- 辺を反転する関手を初頂点に制限して戻した関手との coherent な同型。 -/
def transportStandardInvertingComparisonIso (n : ℕ) {E : SSet.{u}}
    [Quasicategory E]
    (U : nerve (TransportSimplexCategory (Δ[n] : SSet.{u})) ⟶ E)
    (hU : InvertsEdges U (transportSimplexInitialEdges Δ[n])) :
    FunctorIso
      (nerveMap (transportStandardFirstVertex n) ≫
        nerveMap (transportStandardSection n) ≫ U) U := by
  let e := functorEdgeOfSimplicialHomotopy (transportStandardInvertingHomotopy n U)
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk e) :=
    transportStandardInvertingHomotopy_isInvertible n U hU
  exact asIso (SSet.Truncated.HomotopyCategory.homMk e)

/-- 標準切断に沿う制限で、元の標準単体上の実際の関手を得る。 -/
def transportStandardInvertingDescent (n : ℕ) {E : SSet.{u}}
    (U : nerve (TransportSimplexCategory (Δ[n] : SSet.{u})) ⟶ E) : Δ[n] ⟶ E :=
  transportStandardFirstVertexSection n ≫ U

/-- 元の標準単体上の関手は、引き戻してから降ろすと厳密に回収される。 -/
lemma transportStandardInvertingDescent_recover (n : ℕ) {E : SSet.{u}} (V : Δ[n] ⟶ E) :
    transportStandardInvertingDescent n (transportSimplexFirstVertexMap Δ[n] ≫ V) = V := by
  dsimp only [transportStandardInvertingDescent]
  rw [← Category.assoc, transportStandardFirstVertexSection_comp, Category.id_comp]

/-- 降下した関手の引き戻しと、元の辺を反転する関手との coherent な同型。 -/
def transportStandardInvertingDescentIso (n : ℕ) {E : SSet.{u}} [Quasicategory E]
    (U : nerve (TransportSimplexCategory (Δ[n] : SSet.{u})) ⟶ E)
    (hU : InvertsEdges U (transportSimplexInitialEdges Δ[n])) :
    FunctorIso (transportSimplexFirstVertexMap Δ[n] ≫
      transportStandardInvertingDescent n U) U := by
  have h : transportSimplexFirstVertexMap Δ[n] ≫ transportStandardInvertingDescent n U =
      nerveMap (transportStandardFirstVertex n) ≫
        nerveMap (transportStandardSection n) ≫ U := by
    rw [← transportStandardFirstVertex_nerve]
    dsimp only [transportStandardInvertingDescent, transportStandardFirstVertexSection]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]
  exact transportStandardInvertingComparisonIso n U hU

end SerrePositivity.InfinityCategories
