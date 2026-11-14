module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberOctahedronSquares
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexExtension

/-! # 実 Verdier 分母の合成と二対三性

概要：安定閉包に cofiber を持つ辺は合成二単体で二対三性を満たす。
方針：実八面体の最後の列を三辺の cofiber と厳密に同定し、安定閉包の閉性を使う。
規約：二単体を入力し、h の合成だけに置き換えない。使われ方：coherent 分数表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

/-- 全ての実可逆辺は、任意の指定安定閉包に対する cofiber 分母である。 -/
lemma cofiberStableEdges_of_isInvertible (P : Set (X _⦋0⦌)) {a : X _⦋1⦌}
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a)) :
    a ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z} := by
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a)
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_mem_iff P s).mpr
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_zero (s.homMk_isIso_iff_zero.mp ha))

/-- 実合成二単体の三辺は、安定閉包の cofiber 分母として二対三性を満たす。 -/
theorem cofiberStableEdges_twoOfThree (P : Set (X _⦋0⦌)) (τ : Δ[2] ⟶ X) :
    let W := fun i : Fin 3 => SSet.yonedaEquiv (stdSimplex.δ i ≫ τ) ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z}
    (W 2 → W 0 → W 1) ∧ (W 2 → W 1 → W 0) ∧ (W 0 → W 1 → W 2) := by
  dsimp only
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ τ)))
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ s.square = stdSimplex.δ (2 : Fin 3) ≫ τ :=
    s.bottom_edge.trans (SSet.yonedaEquiv.symm_apply_apply _)
  obtain ⟨d⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nonempty_cofiberOctahedronDiagram s.toZeroTriangle s.isPushout τ he
  let t := d.second.rightZeroTriangle
  have h₂ : SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ τ) ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z} ↔
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0) := by
    rw [d.last_source]
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_mem_iff P s
  have h₁ : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ τ) ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z} ↔
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0) := by
    rw [d.last_middle]
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_mem_iff P d.compositeCofiberSquare
  have h₀ : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ τ) ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {z | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P z} ↔
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1) := by
    rw [d.last_target]
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_mem_iff P d.nextCofiberSquare
  refine ⟨fun hf hg => h₁.mpr ?_, fun hf hc => h₀.mpr ?_, fun hg hc => h₂.mpr ?_⟩
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.extension P t d.second.right_isCofiber (h₂.mp hf) (h₀.mp hg)
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_cofiber t d.second.right_isCofiber (h₂.mp hf) (h₁.mp hc)
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_fiber t
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout _ d.second.right_isCofiber) (h₁.mp hc) (h₀.mp hg)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
