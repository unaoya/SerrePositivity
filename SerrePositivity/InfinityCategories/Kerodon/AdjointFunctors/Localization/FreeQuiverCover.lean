module

public import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
public import Mathlib.Combinatorics.Quiver.Covering

/-!
# 元の自由 groupoid の矢を頂点とする根付き quiver

概要：固定根からの元の自由 groupoid の矢を頂点とする持ち上げ quiver を構成する。
方針：元の生成矢の右合成で持ち上げた矢の終点を指定する。
規約：元の基底頂点・元の生成矢・元の groupoid の矢を保持する。
使われ方：全指定自由圏の hammock の成分の普遍被覆。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q]

structure Vertex (A : Q) where
  base : Q
  path : (Quiver.FreeGroupoid.of Q).obj A ⟶ (Quiver.FreeGroupoid.of Q).obj base

variable (A : Q)

@[instance_reducible]
def quiver : Quiver.{v} (Vertex A) where
  Hom x y := {f : x.base ⟶ y.base // x.path ≫ (Quiver.FreeGroupoid.of Q).map f = y.path}

def projection : letI := quiver A; Vertex A ⥤q Q := by
  letI := quiver A
  exact { obj := Vertex.base, map := fun f => f.val }

def root : Vertex A := ⟨A, 𝟙 _⟩

def forwardTarget (x : Vertex A) {B : Q} (f : x.base ⟶ B) : Vertex A :=
  ⟨B, x.path ≫ (Quiver.FreeGroupoid.of Q).map f⟩

def forwardArrow (x : Vertex A) {B : Q} (f : x.base ⟶ B) :
    letI := quiver A
    x ⟶ forwardTarget A x f := by
  letI := quiver A
  exact ⟨f, rfl⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover
