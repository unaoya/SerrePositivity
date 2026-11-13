module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.LiftedShapeNerveIso
public import Mathlib.Data.Fintype.EquivFin

/-!
概要：元の離散添字の全単射から、元の持ち上げた nerve の厳密な同型を構成する。
方針：全単射と逆写像を厳密な逆関手にし、元の頂点への作用を保持する。
規約：添字の選択を明示し、元の図式を等式で照合する。
使われ方：有限 coherent 積比較の一般有限添字への再添字。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の離散添字の全単射による nerve の厳密な同型。 -/
def discreteIndexNerveIso {J L : Type u} (e : J ≃ L) :
    nerve (Discrete J) ≅ nerve (Discrete L) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nerveIsoOfStrictInverse (Discrete.functor (fun j ↦ Discrete.mk (e j)))
    (Discrete.functor (fun l ↦ Discrete.mk (e.symm l)))
    (CategoryTheory.Functor.ext
      (fun j ↦ congrArg Discrete.mk (e.symm_apply_apply j.as))
      (fun _ _ _ ↦ Subsingleton.elim _ _))
    (CategoryTheory.Functor.ext
      (fun l ↦ congrArg Discrete.mk (e.apply_symm_apply l.as))
      (fun _ _ _ ↦ Subsingleton.elim _ _))

/-- 同じ添字の全単射を、元の持ち上げた離散 nerve の同型にする。 -/
def liftedDiscreteIndexIso {J L : Type u} (e : J ≃ L) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ≅
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete L)) :=
  (SSet.uliftFunctor.{u + 1, u}).mapIso (discreteIndexNerveIso e)

/-- 持ち上げた同型は、元の指定添字の頂点を元の像の頂点へ厳密に送る。 -/
lemma liftedDiscreteIndexIso_vertex {J L : Type u} (e : J ≃ L) (j : J) :
    (liftedDiscreteIndexIso e).hom.app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j))) =
        ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk (e j))) := rfl

/-- 任意の非空有限添字は、元の小さい宇宙で非空有限標準添字と全単射を持つ。 -/
lemma nonemptyFiniteIndex_exists_equiv (J : Type u) [Finite J] [Nonempty J] :
    ∃ n : ℕ, Nonempty (J ≃ ULift.{u} (Fin (n + 1))) := by
  let := Fintype.ofFinite J
  have h : 0 < Fintype.card J := Fintype.card_pos
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  exact ⟨n, ⟨(Fintype.equivFinOfCardEq hn).trans Equiv.ulift.symm⟩⟩

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
