module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSimplexEdgeEndpoint

/-!
概要：指定された可算辺列を含む、厳密に整合する全単体の列を構成する。
方針：標準輸送による全単体の延長を自然数上で反復する。
規約：指定辺の代表を変更せず、高次の整合を同時に選ぶ。
使われ方：交互列を元の可算 nerve 上の coherent 図式へ貼り合わせる準備。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：任意の指定可算辺列は、全ての有限始区間の整合する全単体に延長できる。
方針：指定された最初の辺から始め、終点を保つ全単体延長を反復する。
規約：各有限単体の全体を前段階への制限で厳密に回収する。
使われ方：元の辺列から coherent な可算図式を構成する。 -/
lemma exists_sequentialEdgeSimplices {X : SSet.{u}} [Quasicategory X]
    (x : ℕ → X _⦋0⦌) (e : ∀ n, X.Edge (x n) (x (n + 1))) :
    ∃ f : ∀ n, (Δ[n + 1] : SSet.{u}) ⟶ X,
      f 0 = SSet.yonedaEquiv.symm (e 0).edge ∧
      (∀ n, SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front (n + 1)) ≫ f (n + 1) = f n) ∧
      (∀ n, (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexTerminalCocone n (f n)).vertex = x (n + 1)) ∧
      ∀ n, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom) ≫
        f (n + 1) = SSet.yonedaEquiv.symm (e (n + 1)).edge := by
  let A (n : ℕ) := {f : (Δ[n + 1] : SSet.{u}) ⟶ X //
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexTerminalCocone n f).vertex = x (n + 1)}
  have h₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexTerminalCocone 0 (SSet.yonedaEquiv.symm (e 0).edge)).vertex = x 1 := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexTerminalCocone_vertex]
    have hv : SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex 0) =
        SSet.stdSimplex.δ (0 : Fin 2) := by
      apply SSet.yonedaEquiv.injective
      apply SSet.stdSimplex.ext
      intro i
      fin_cases i
      rfl
    rw [hv, (e 0).δ_zero_yonedaEquiv_symm, Equiv.apply_symm_apply]
  let a₀ : A 0 := ⟨SSet.yonedaEquiv.symm (e 0).edge, h₀⟩
  let edge (n : ℕ) (a : A n) : X.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexTerminalCocone n a.val).vertex
      (x (n + 2)) :=
    ⟨(e (n + 1)).edge, (e (n + 1)).src_eq.trans a.property.symm, (e (n + 1)).tgt_eq⟩
  let next (n : ℕ) (a : A n) : A (n + 1) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexSpecifiedEdgeExtension n a.val (edge n a),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexSpecifiedEdgeExtension_vertex n a.val (edge n a)⟩
  let a : ∀ n, A n := fun n ↦ Nat.rec a₀ next n
  refine ⟨fun n ↦ (a n).val, rfl, ?_, fun n ↦ (a n).property, ?_⟩
  · intro n
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexSpecifiedEdgeExtension_front n (a n).val (edge n (a n))
  · intro n
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexSpecifiedEdgeExtension_lastEdge n (a n).val (edge n (a n))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
