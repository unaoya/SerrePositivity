module

public import SerrePositivity.KST.LocalizingInvariants.FullStableClosure
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport

/-!
概要：安定閉条件の全部分圏の元の包含は完全関手。
方針：周囲で選んだ cofiber を部分圏へ戻し、任意の cofiber と同じ辺の四角形同型で比較する。
規約：部分圏の普遍性から周囲の普遍性への向きを入力しない。使われ方：通常 pullback の完全包含。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.FullSubcomplex

variable {X : SSet.{u}} [Quasicategory X] [IsStable X]
  (P : X _⦋0⦌ → Prop) (hP : _root_.SerrePositivity.InfinityCategories.Stable.Exact.StableVertexCondition P)

include hP in
lemma inclusion_isExact : IsExactFunctor (fullSubcomplexOnVertices X P).ι where
  preservesZero := inclusion_preservesZero P hP
  preservesCofiber t ht := by
    let f := edgeOfSimplex (SSet.yonedaEquiv (squareBottomEdge ≫ t.square))
    let d : CofiberSquare f := {
      toZeroTriangle := t
      bottom_edge := (SSet.yonedaEquiv.symm_apply_apply _).symm
      isPushout := ht }
    let s := chosenCofiberSquare (f.map ((truncation 2).map (fullSubcomplexOnVertices X P).ι))
    let r := cofiberLift P f s (_root_.SerrePositivity.InfinityCategories.Stable.Exact.FullSubcomplex.cofiber_vertices P hP f s)
    obtain ⟨e⟩ := nonempty_cofiberSquareFunctorIso r d
    have hr : IsPushoutSquare (r.square ≫ (fullSubcomplexOnVertices X P).ι) := by
      change IsPushoutSquare (squareLift P s.square (_root_.SerrePositivity.InfinityCategories.Stable.Exact.FullSubcomplex.cofiber_vertices P hP f s) ≫ _)
      rw [squareLift_ι]
      exact s.isPushout
    exact hr.of_functorIso (FunctorIso.postcomp e (fullSubcomplexOnVertices X P).ι)

end SerrePositivity.KST.LocalizingInvariants.FullSubcomplex
