module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeSimplexEdgeExtension
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialDiagramFiniteStages

/-!
概要：指定された基底の可算図式に沿い、全有限始区間の持ち上げを選ぶ。
方針：最後の指定辺と基底の全単体を保つ相対延長を反復する。
規約：辺の射影だけでなく全有限単体の射影を固定する。
使われ方：元の対象の上での交互表示の coherent 実現。

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

/-- 概要：基底の全図式と指定辺列を同時に保つ整合した全単体列が存在する。
方針：有限全単体の相対延長を始区間に沿って反復する。
規約：基底と元の標的は quasicategory、射は inner fibration。
使われ方：引き戻しの交互列を基底上で貼り合わせる。 -/
lemma exists_relativeSequentialEdgeSimplices {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    (x : ℕ → X _⦋0⦌) (e : ∀ n, X.Edge (x n) (x (n + 1)))
    (H : nerve (ULift.{u} ℕ) ⟶ Y)
    (he : ∀ n, SSet.yonedaEquiv.symm (e n).edge ≫ p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSuccessorEdge n ≫ H) :
    ∃ f : ∀ n, (Δ[n + 1] : SSet.{u}) ⟶ X,
      f 0 = SSet.yonedaEquiv.symm (e 0).edge ∧
      (∀ n, SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front (n + 1)) ≫ f (n + 1) = f n) ∧
      (∀ n, f n ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (n + 1) ≫ H) ∧
      ∀ n, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom) ≫
        f (n + 1) = SSet.yonedaEquiv.symm (e (n + 1)).edge := by
  let A (n : ℕ) := {f : (Δ[n + 1] : SSet.{u}) ⟶ X //
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexTerminalCocone n f).vertex = x (n + 1) ∧
      f ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (n + 1) ≫ H}
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
  let a₀ : A 0 := ⟨SSet.yonedaEquiv.symm (e 0).edge, h₀, he 0⟩
  let edge (n : ℕ) (a : A n) : X.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexTerminalCocone n a.val).vertex
      (x (n + 2)) :=
    ⟨(e (n + 1)).edge, (e (n + 1)).src_eq.trans a.property.1.symm,
      (e (n + 1)).tgt_eq⟩
  have hnext (n : ℕ) (a : A n) : ∃ b : A (n + 1),
      SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front (n + 1)) ≫ b.val = a.val ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom) ≫ b.val =
        SSet.yonedaEquiv.symm (e (n + 1)).edge := by
    obtain ⟨g, hg, hge, hgp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_relativeSimplex_edge_extension p n a.val (edge n a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (n + 2) ≫ H)
      (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex_front, a.property.2])
      (by
        change _ = SSet.yonedaEquiv.symm (e (n + 1)).edge ≫ p
        simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSuccessorEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex,
          Category.assoc] using (he (n + 1)).symm)
    refine ⟨⟨g, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexTerminalCocone_vertex_of_lastEdge n g (edge n a) hge, hgp⟩,
      hg, hge⟩
  let next (n : ℕ) (a : A n) : A (n + 1) := (hnext n a).choose
  let a : ∀ n, A n := fun n ↦ Nat.rec a₀ next n
  exact ⟨fun n ↦ (a n).val, rfl, fun n ↦ (hnext n (a n)).choose_spec.1,
    fun n ↦ (a n).property.2, fun n ↦ (hnext n (a n)).choose_spec.2⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
