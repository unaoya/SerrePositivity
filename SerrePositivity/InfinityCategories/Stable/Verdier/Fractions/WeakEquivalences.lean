module
public import SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence
public import SerrePositivity.InfinityCategories.Stable.CofiberCompositionEdges
public import SerrePositivity.InfinityCategories.Stable.CofiberLocalizingBaseChange

/-! # Verdier 列の Waldhausen 弱同値

cofiber が包含の本質像に属する実辺を使う。商の核条件から本質像が既に
安定閉包であることを証明し、実二単体の二対三性と実押し出しの安定性を得る。
厚さの追加条件や商の冪等完備化はこの工程には不要である。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 選択に依存しない、包含の本質像に cofiber を持つ実辺。 -/
def weakEquivalences {A B : StableCategory.{u}} (i : ExactMap A B) :
    Set (B.obj _⦋1⦌) := cofiberLocalizingEdges (essentialImage i)

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}

/-- 商の核は零・同型・cofiber・fiber で閉じている。 -/
lemma stableClosure_essentialImage (h : IsVerdierSequence i q) :
    {x | StableVertexClosure (essentialImage i) x} = essentialImage i := by
  ext x
  exact ⟨fun hx => (h.kernel x).1
    (kills_stableVertexClosure q.hom (essentialImage i)
      (fun y hy => (h.kernel y).2 hy) hx), StableVertexClosure.of_mem⟩

/-- 指定した cofiber で W 所属を判定できる。 -/
lemma mem_weakEquivalences_iff (h : IsVerdierSequence i q)
    {x y : B.obj _⦋0⦌}
    {f : Truncated.Edge (X := (truncation 2).obj B.obj) x y}
    (s : CofiberSquare f) :
    f.edge ∈ weakEquivalences i ↔ s.cofiber ∈ essentialImage i := by
  have hs := cofiberStableEdges_edge_mem_iff (essentialImage i) s
  change f.edge ∈ cofiberLocalizingEdges {z | StableVertexClosure (essentialImage i) z} ↔
    s.cofiber ∈ {z | StableVertexClosure (essentialImage i) z} at hs
  rw [stableClosure_essentialImage h] at hs
  exact hs

/-- W は商で可逆となる実辺のクラスに等しい。 -/
lemma mem_weakEquivalences_iff_invertible (h : IsVerdierSequence i q)
    {x y : B.obj _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj B.obj) x y) :
    f.edge ∈ weakEquivalences i ↔
      IsInvertibleEdge (f.map ((truncation 2).map q.hom)) := by
  let s := chosenCofiberSquare f
  rw [mem_weakEquivalences_iff h s, ← h.kernel s.cofiber]
  exact (s.map_isInvertible_iff_zero q.hom).symm

/-- 実合成二単体を保つ二対三性。 -/
theorem weakEquivalences_twoOfThree (h : IsVerdierSequence i q) (τ : Δ[2] ⟶ B.obj) :
    let W := fun j : Fin 3 => SSet.yonedaEquiv (stdSimplex.δ j ≫ τ) ∈
      weakEquivalences i
    (W 2 → W 0 → W 1) ∧ (W 2 → W 1 → W 0) ∧ (W 0 → W 1 → W 2) := by
  simpa only [weakEquivalences, stableClosure_essentialImage h] using
    cofiberStableEdges_twoOfThree (essentialImage i) τ

/-- 実押し出しに沿って W 所属は保存され、反映される。 -/
theorem weakEquivalences_pushout_iff (h : IsVerdierSequence i q)
    (L : Δ[1] ⊗ Δ[1] ⟶ B.obj) (hL : IsPushoutSquare L) :
    (squareLeftArrow L).edge ∈ weakEquivalences i ↔
      (squareRightArrow L).edge ∈ weakEquivalences i := by
  simpa only [weakEquivalences, stableClosure_essentialImage h] using
    cofiberStableEdges_pushout_iff (essentialImage i) L hL

/-- 安定性による引き戻し版。 -/
theorem weakEquivalences_pullback_iff (h : IsVerdierSequence i q)
    (L : Δ[1] ⊗ Δ[1] ⟶ B.obj) (hL : IsPullbackSquare L) :
    (squareLeftArrow L).edge ∈ weakEquivalences i ↔
      (squareRightArrow L).edge ∈ weakEquivalences i := by
  simpa only [weakEquivalences, stableClosure_essentialImage h] using
    cofiberStableEdges_pullback_iff (essentialImage i) L hL

end SerrePositivity.KST.Fibration
