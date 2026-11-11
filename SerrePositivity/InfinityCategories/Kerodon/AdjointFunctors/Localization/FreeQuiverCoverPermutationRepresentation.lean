module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverGeneratorPermutations
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.GroupTheory.Perm.Basic

/-!
# 元の自由 groupoid の持ち上げ射の集合上の置換表現

概要：元の生成矢の持ち上げ置換を元の自由 groupoid の全射へ延長する。
方針：元の自由 groupoid の普遍性を置換群の一対象 groupoid へ適用する。
規約：逆対は元の置換の逆操作として扱い、忠実性を入力にしない。
使われ方：射影で同じ射を同じ持ち上げ射へ回収する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

def permutationPrefunctor :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ S : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A), Q ⥤q SingleObj (Equiv.Perm (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LiftStar A S)) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S
  exact { obj := fun _ => SingleObj.star _, map := fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorPermutation A S f }

def permutationRepresentation :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ S : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A),
      Quiver.FreeGroupoid Q ⥤ SingleObj (Equiv.Perm (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LiftStar A S)) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S
  exact Quiver.FreeGroupoid.lift (permutationPrefunctor A S)

lemma permutationRepresentation_generator :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ (S : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) {B E : Q} (f : B ⟶ E),
      (permutationRepresentation A S).map ((Quiver.FreeGroupoid.of Q).map f) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorPermutation A S f := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S B E f
  rfl

def starRepresentation :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ S : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A),
      Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) ⥤ SingleObj (Equiv.Perm (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LiftStar A S)) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidProjection A ⋙ permutationRepresentation A S

lemma starRepresentation_generator :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ (S : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A} (f : x ⟶ y),
      (starRepresentation A S).map ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).map f) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorPermutation A S f.val := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S x y f
  rfl

def starPermutation :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ (S : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) {x y : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)},
      (x ⟶ y) → Equiv.Perm (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LiftStar A S) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro S x y f
  exact (starRepresentation A S).map f

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
