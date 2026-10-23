module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldRestriction
public import SerrePositivity.InfinityCategories.F1.Cocartesian.LiftPreservation
public import SerrePositivity.InfinityCategories.F1B.KanUniversalScaffoldFiber
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianStrictTransportEquivalence

/-!
概要：universal scaffold の水平辺により、全 cocartesian 辺の保存を検出する。
方針：恒等射評価の厳密な切断で各始点の section を取り、同じ底の水平 lift と比較する。
規約：元の射と元の cocartesian 辺の保存を判定し、標的に left fibration 性は要求しない。
使われ方：scaffold 制限の全部分複体条件の反映と、写像空間比較の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- replacement の水平辺の始点は、同じ係数頂点の定値な底への標準包含。 -/
lemma kanScaffoldHorizontalEdge_source {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) (x : (F.obj c) _⦋0⦌) :
    (simplicialReplacement F).δ 1 (kanScaffoldHorizontalEdge F f x) =
      (simplicialReplacementConstantLift F c).app (Opposite.op ⦋0⦌) x := by
  refine Sigma.ext (ComposableArrows.ext₀ rfl) ?_
  apply heq_of_eq
  change stdSimplex.δ 1 ≫ SSet.const x ≫ F.map (𝟙 c) = SSet.yonedaEquiv.symm x
  rw [F.map_id, Category.comp_id, SSet.comp_const, SSet.yonedaEquiv_symm_zero]

/-- 任意の fiber の元の頂点を、恒等射評価で厳密に持つ cocartesian section を取れる。 -/
lemma exists_cocartesianStrictTransport_with_value {C : Type u} [Category.{u} C]
    {E : SSet.{u}} (p : E ⟶ nerve C) [CocartesianFibration p]
    (c : C) (x : E _⦋0⦌) (hx : p.app (Opposite.op ⦋0⦌) x = nerveVertex c) :
    ∃ s : (kanCocartesianStrictTransport p c) _⦋0⦌,
      ((kanCocartesianStrictTransportEvaluate p c).app (Opposite.op ⦋0⦌) s).val = x := by
  let v : (vertexFiber p (nerveVertex c)) _⦋0⦌ :=
    ⟨x, by rw [pinchedConstant_zero]; exact hx⟩
  obtain ⟨r, hr⟩ := trivialKanFibration_exists_section (kanCocartesianStrictTransportEvaluate p c)
  refine ⟨r.app (Opposite.op ⦋0⦌) v, ?_⟩
  exact congrArg Subtype.val (congrArg (fun H => H.app (Opposite.op ⦋0⦌) v) hr)

/-- 各辺と同じ始点を持つ universal scaffold の水平 lift を選べる。 -/
lemma exists_kanUniversalScaffold_horizontal_with_source {C : Type u} [Category.{u} C]
    {E : SSet.{u}} (p : E ⟶ nerve C) [CocartesianFibration p] (e : E _⦋1⦌) :
    ∃ s : (kanCocartesianStrictTransport p
        ((p.app (Opposite.op ⦋1⦌) e).obj 0)) _⦋0⦌,
      E.δ 1 ((kanUniversalScaffold p).app (Opposite.op ⦋1⦌)
        (kanScaffoldHorizontalEdge (kanCocartesianStrictTransportDiagram p)
          (p.app (Opposite.op ⦋1⦌) e).hom s)) = E.δ 1 e := by
  let σ := p.app (Opposite.op ⦋1⦌) e
  have hx : p.app (Opposite.op ⦋0⦌) (E.δ 1 e) = nerveVertex (σ.obj 0) := by
    have hn := ConcreteCategory.congr_hom (p.naturality (SimplexCategory.δ (1 : Fin 2)).op) e
    change p.app (Opposite.op ⦋0⦌) (E.δ 1 e) = (nerve C).δ 1 σ at hn
    exact hn.trans (show (nerve C).δ 1 σ = nerveVertex (σ.obj 0) from
      ComposableArrows.ext₀ rfl)
  obtain ⟨s, hs⟩ := exists_cocartesianStrictTransport_with_value p (σ.obj 0) (E.δ 1 e) hx
  refine ⟨s, ?_⟩
  have hn := ConcreteCategory.congr_hom
    ((kanUniversalScaffold p).naturality (SimplexCategory.δ (1 : Fin 2)).op)
    (kanScaffoldHorizontalEdge (kanCocartesianStrictTransportDiagram p) σ.hom s)
  change (kanUniversalScaffold p).app (Opposite.op ⦋0⦌)
      ((simplicialReplacement (kanCocartesianStrictTransportDiagram p)).δ 1
        (kanScaffoldHorizontalEdge (kanCocartesianStrictTransportDiagram p) σ.hom s)) =
    E.δ 1 ((kanUniversalScaffold p).app (Opposite.op ⦋1⦌)
      (kanScaffoldHorizontalEdge (kanCocartesianStrictTransportDiagram p) σ.hom s)) at hn
  rw [kanScaffoldHorizontalEdge_source] at hn
  have he := congrArg (fun H => H.app (Opposite.op ⦋0⦌) s)
    (simplicialReplacementConstantLift_kanUniversalScaffold p (σ.obj 0))
  change (kanUniversalScaffold p).app (Opposite.op ⦋0⦌)
      ((simplicialReplacementConstantLift (kanCocartesianStrictTransportDiagram p) (σ.obj 0)).app
        (Opposite.op ⦋0⦌) s) =
    ((kanCocartesianStrictTransportEvaluate p (σ.obj 0)).app (Opposite.op ⦋0⦌) s).val at he
  exact hn.symm.trans (he.trans hs)

/-- universal scaffold の水平辺を保つ実際の射は、全ての cocartesian 辺を保つ。 -/
lemma preservesCocartesianEdges_of_kanUniversalScaffold_horizontal
    {C : Type u} [Category.{u} C] {E D : SSet.{u}}
    (p : E ⟶ nerve C) (q : D ⟶ nerve C) [CocartesianFibration p] [InnerFibration q]
    (g : E ⟶ D)
    (hc : ∀ {c d : C} (f : c ⟶ d) (x : (kanCocartesianStrictTransport p c) _⦋0⦌),
      IsCocartesianEdge q ((kanUniversalScaffold p ≫ g).app (Opposite.op ⦋1⦌)
        (kanScaffoldHorizontalEdge (kanCocartesianStrictTransportDiagram p) f x))) :
    PreservesCocartesianEdges p q g := by
  letI : Quasicategory E := quasicategory_of_innerFibration p
  letI : Quasicategory D := quasicategory_of_innerFibration q
  apply preservesCocartesianEdges_of_matching_lifts p q g
  intro e
  obtain ⟨s, hs⟩ := exists_kanUniversalScaffold_horizontal_with_source p e
  let σ := p.app (Opposite.op ⦋1⦌) e
  let h := (kanUniversalScaffold p).app (Opposite.op ⦋1⦌)
    (kanScaffoldHorizontalEdge (kanCocartesianStrictTransportDiagram p) σ.hom s)
  refine ⟨h, hs, ?_, kanUniversalScaffold_horizontal p σ.hom s, hc σ.hom s⟩
  have hp := congrArg (fun H => H.app (Opposite.op ⦋1⦌)
    (kanScaffoldHorizontalEdge (kanCocartesianStrictTransportDiagram p) σ.hom s))
    (kanUniversalScaffold_projection p)
  exact hp.trans (ComposableArrows.mk₁_hom σ)

end SerrePositivity.InfinityCategories
