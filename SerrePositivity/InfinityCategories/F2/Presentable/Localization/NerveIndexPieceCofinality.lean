module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.NerveIndexPiece
public import SerrePositivity.InfinityCategories.F2.Presentable.NerveFinalInitialComma

/-!
概要：実添字列は、種集合を含む部分 poset の nerve へも right cofinal に入る。
方針：各右 comma で、指定頂点を最初に支配する自然数項を始対象に取る。
規約：通常の final 性だけで止めず、元の全 nerve 写像の cofinal 性を得る。
使われ方：元の部分表示の指定余極限を同じ可算列で計算する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization

/-- 元の同じ実添字列は、種集合を含む部分 poset の全 nerve に right cofinal。 -/
lemma nerveIndexPiece_nerve_isRightCofinal {A : Type u} [Preorder A]
    (seed : Set A) (J : nerve (ULift.{u} ℕ) ⟶ nerve A)
    (hseed : ∀ x ∈ seed, x ≤ nerveIndexSequence J 0) :
    IsRightCofinal (nerveMap (nerveIndexPieceMonotone seed J).functor) := by
  classical
  apply nerveMap_isRightCofinal_of_initial_comma
  intro x
  let h := sequentialPiece_exists_le seed (nerveIndexSequence J) hseed x
  let n := Nat.find h
  let F := (nerveIndexPieceMonotone seed J).functor
  let f : x ⟶ F.obj (ULift.up n) := homOfLE (Nat.find_spec h)
  refine ⟨StructuredArrow.mk f, ⟨IsInitial.ofUniqueHom (fun y ↦ ?_) ?_⟩⟩
  · have hy : x.val ≤ nerveIndexSequence J y.right.down := leOfHom y.hom
    have hn : (ULift.up n : ULift.{u} ℕ) ≤ y.right := Nat.find_min' h hy
    exact StructuredArrow.homMk (homOfLE hn) (by subsingleton)
  · intro y g
    apply StructuredArrow.hom_ext
    exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
