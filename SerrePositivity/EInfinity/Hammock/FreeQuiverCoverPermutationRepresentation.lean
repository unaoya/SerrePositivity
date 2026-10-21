module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverGeneratorPermutations
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.GroupTheory.Perm.Basic

/-!
# 元の自由 groupoid の持ち上げ射の集合上の置換表現

概要：元の生成矢の持ち上げ置換を元の自由 groupoid の全射へ延長する。
方針：元の自由 groupoid の普遍性を置換群の一対象 groupoid へ適用する。
規約：逆対は元の置換の逆操作として扱い、忠実性を入力にしない。
使われ方：射影で同じ射を同じ持ち上げ射へ回収する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

def permutationPrefunctor :
    letI := quiver A
    ∀ S : Quiver.FreeGroupoid (Vertex A), Q ⥤q SingleObj (Equiv.Perm (LiftStar A S)) := by
  letI := quiver A
  intro S
  exact { obj := fun _ => SingleObj.star _, map := fun f => generatorPermutation A S f }

def permutationRepresentation :
    letI := quiver A
    ∀ S : Quiver.FreeGroupoid (Vertex A),
      Quiver.FreeGroupoid Q ⥤ SingleObj (Equiv.Perm (LiftStar A S)) := by
  letI := quiver A
  intro S
  exact Quiver.FreeGroupoid.lift (permutationPrefunctor A S)

lemma permutationRepresentation_generator :
    letI := quiver A
    ∀ (S : Quiver.FreeGroupoid (Vertex A)) {B E : Q} (f : B ⟶ E),
      (permutationRepresentation A S).map ((Quiver.FreeGroupoid.of Q).map f) =
        generatorPermutation A S f := by
  let := quiver A
  intro S B E f
  rfl

def starRepresentation :
    letI := quiver A
    ∀ S : Quiver.FreeGroupoid (Vertex A),
      Quiver.FreeGroupoid (Vertex A) ⥤ SingleObj (Equiv.Perm (LiftStar A S)) := by
  letI := quiver A
  intro S
  exact groupoidProjection A ⋙ permutationRepresentation A S

lemma starRepresentation_generator :
    letI := quiver A
    ∀ (S : Quiver.FreeGroupoid (Vertex A)) {x y : Vertex A} (f : x ⟶ y),
      (starRepresentation A S).map ((Quiver.FreeGroupoid.of (Vertex A)).map f) =
        generatorPermutation A S f.val := by
  let := quiver A
  intro S x y f
  rfl

def starPermutation :
    letI := quiver A
    ∀ (S : Quiver.FreeGroupoid (Vertex A)) {x y : Quiver.FreeGroupoid (Vertex A)},
      (x ⟶ y) → Equiv.Perm (LiftStar A S) := by
  letI := quiver A
  intro S x y f
  exact (starRepresentation A S).map f

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
