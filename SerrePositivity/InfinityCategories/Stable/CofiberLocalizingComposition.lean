module
public import SerrePositivity.InfinityCategories.Stable.CofiberOctahedronSquares
public import SerrePositivity.InfinityCategories.Stable.StableVertexExtension

/-! # 実 Verdier 分母の合成と二対三性

概要：安定閉包に cofiber を持つ辺は合成二単体で二対三性を満たす。
方針：実八面体の最後の列を三辺の cofiber と厳密に同定し、安定閉包の閉性を使う。
規約：二単体を入力し、h の合成だけに置き換えない。使われ方：coherent 分数表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {X : SSet.{u}} [Quasicategory X] [IsStable X]

/-- 全ての実可逆辺は、任意の指定安定閉包に対する cofiber 分母である。 -/
lemma cofiberStableEdges_of_isInvertible (P : Set (X _⦋0⦌)) {a : X _⦋1⦌}
    (ha : IsInvertibleEdge (edgeOfSimplex a)) :
    a ∈ cofiberLocalizingEdges {z | StableVertexClosure P z} := by
  let s := chosenCofiberSquare (edgeOfSimplex a)
  exact (cofiberStableEdges_mem_iff P s).mpr
    (StableVertexClosure.of_zero (s.homMk_isIso_iff_zero.mp ha))

/-- 実合成二単体の三辺は、安定閉包の cofiber 分母として二対三性を満たす。 -/
theorem cofiberStableEdges_twoOfThree (P : Set (X _⦋0⦌)) (τ : Δ[2] ⟶ X) :
    let W := fun i : Fin 3 => SSet.yonedaEquiv (stdSimplex.δ i ≫ τ) ∈
      cofiberLocalizingEdges {z | StableVertexClosure P z}
    (W 2 → W 0 → W 1) ∧ (W 2 → W 1 → W 0) ∧ (W 0 → W 1 → W 2) := by
  dsimp only
  let s := chosenCofiberSquare
    (edgeOfSimplex (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ τ)))
  have he : squareBottomEdge ≫ s.square = stdSimplex.δ (2 : Fin 3) ≫ τ :=
    s.bottom_edge.trans (SSet.yonedaEquiv.symm_apply_apply _)
  obtain ⟨d⟩ := nonempty_cofiberOctahedronDiagram s.toZeroTriangle s.isPushout τ he
  let t := d.second.rightZeroTriangle
  have h₂ : SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ τ) ∈
      cofiberLocalizingEdges {z | StableVertexClosure P z} ↔
      StableVertexClosure P (squareVertex t.square 0 0) := by
    rw [d.last_source]
    exact cofiberStableEdges_mem_iff P s
  have h₁ : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ τ) ∈
      cofiberLocalizingEdges {z | StableVertexClosure P z} ↔
      StableVertexClosure P (squareVertex t.square 1 0) := by
    rw [d.last_middle]
    exact cofiberStableEdges_mem_iff P d.compositeCofiberSquare
  have h₀ : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ τ) ∈
      cofiberLocalizingEdges {z | StableVertexClosure P z} ↔
      StableVertexClosure P (squareVertex t.square 1 1) := by
    rw [d.last_target]
    exact cofiberStableEdges_mem_iff P d.nextCofiberSquare
  refine ⟨fun hf hg => h₁.mpr ?_, fun hf hc => h₀.mpr ?_, fun hg hc => h₂.mpr ?_⟩
  · exact StableVertexClosure.extension P t d.second.right_isCofiber (h₂.mp hf) (h₀.mp hg)
  · exact StableVertexClosure.of_cofiber t d.second.right_isCofiber (h₂.mp hf) (h₁.mp hc)
  · exact StableVertexClosure.of_fiber t
      (IsStable.pullback_of_pushout _ d.second.right_isCofiber) (h₁.mp hc) (h₀.mp hg)

end SerrePositivity.InfinityCategories
