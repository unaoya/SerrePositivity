module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NerveIndexSequence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialPieces
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
概要：元の poset の全添字図式を、種集合と同じ実頂点列の和へ因子化する。
方針：nerve の充満性で元の関手を回収し、元の全頂点でその像を比較する。
規約：元の図式の全射を保持する。使われ方：共通小部分表示の共終な可算添字。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {A : Type u} [Preorder A]

/-- 元の全添字図式を定める、元の poset 内の通常関手。 -/
def nerveIndexFunctor (J : nerve (ULift.{u} ℕ) ⟶ nerve A) : ULift.{u} ℕ ⥤ A :=
  (nerveFunctor.preimage (X := Cat.of (ULift.{u} ℕ)) (Y := Cat.of A) J).toFunctor

/-- 元の全添字図式は、回収した同じ関手の nerve そのものである。 -/
lemma nerveIndexFunctor_nerveMap (J : nerve (ULift.{u} ℕ) ⟶ nerve A) :
    nerveMap (nerveIndexFunctor J) = J :=
  nerveFunctor.map_preimage (X := Cat.of (ULift.{u} ℕ)) (Y := Cat.of A) J

/-- 回収した通常関手は、元の同じ実頂点列を取る。 -/
lemma nerveIndexFunctor_obj (J : nerve (ULift.{u} ℕ) ⟶ nerve A) (n : ℕ) :
    (nerveIndexFunctor J).obj (ULift.up n) = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveIndexSequence J n := by
  have h := congrArg (fun F : nerve (ULift.{u} ℕ) ⟶ nerve A ↦
    nerveEquiv (F.app (Opposite.op ⦋0⦌)
      ((nerveEquiv (C := ULift.{u} ℕ)).symm (ULift.up n)))) (nerveIndexFunctor_nerveMap J)
  exact h

/-- 元の同じ列を、種集合を含む小さい部分 poset の中で読む。 -/
def nerveIndexPieceMonotone (seed : Set A) (J : nerve (ULift.{u} ℕ) ⟶ nerve A) :
    Monotone (fun n : ULift.{u} ℕ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialPieceSequence seed (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveIndexSequence J) n.down) :=
  fun _ _ h ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveIndexSequence_monotone J h

/-- 種集合と実頂点列の和から、元の poset への包含関手。 -/
def sequentialPieceInclusionFunctor (seed : Set A) (a : ℕ → A) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialPiece seed a ⥤ A where
  obj x := x.val
  map f := homOfLE (leOfHom f)

/-- 元の添字図式の全射は、同じ小さい部分 poset への因子化でも厳密に残る。 -/
lemma nerveIndexPiece_factorization (seed : Set A) (J : nerve (ULift.{u} ℕ) ⟶ nerve A) :
    nerveMap (nerveIndexPieceMonotone seed J).functor ≫
      nerveMap (sequentialPieceInclusionFunctor seed (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveIndexSequence J)) = J := by
  have h : (nerveIndexPieceMonotone seed J).functor ⋙
      sequentialPieceInclusionFunctor seed (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveIndexSequence J) = nerveIndexFunctor J := by
    apply CategoryTheory.Functor.ext (fun n ↦ (nerveIndexFunctor_obj J n.down).symm)
  change nerveMap ((nerveIndexPieceMonotone seed J).functor ⋙
    sequentialPieceInclusionFunctor seed (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveIndexSequence J)) = J
  rw [h, nerveIndexFunctor_nerveMap]

/-- 初項が種集合を支配すれば、同じ実添字列は部分 poset の中で final となる。 -/
lemma nerveIndexPiece_final (seed : Set A) (J : nerve (ULift.{u} ℕ) ⟶ nerve A)
    (hseed : ∀ x ∈ seed, x ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveIndexSequence J 0) :
    (nerveIndexPieceMonotone seed J).functor.Final := by
  apply (Monotone.final_functor_iff (nerveIndexPieceMonotone seed J)).mpr
  intro x
  obtain ⟨n, hn⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialPiece_exists_le seed (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveIndexSequence J) hseed x
  exact ⟨ULift.up n, hn⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
