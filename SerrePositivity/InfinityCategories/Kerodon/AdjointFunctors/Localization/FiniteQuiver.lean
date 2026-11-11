module

public import Mathlib.CategoryTheory.Category.Quiv
public import Mathlib.Data.Finset.Basic

/-!
# 元の有限頂点集合に誘導された quiver と自由圏

概要：元の頂点部分型と元の生成辺を使う quiver を構成する。
方針：生成辺を変更せず、頂点の所属証明だけを加える。
規約：quiver は局所的に選び、大域 instance を追加しない。
使われ方：有限部分木の自由圏と葉を除く関手。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q]

def Vertex (S : Finset Q) := {x : Q // x ∈ S}

@[instance_reducible] def quiver (S : Finset Q) : Quiver.{v} (Vertex S) where
  Hom x y := x.val ⟶ y.val

def inclusion (S : Finset Q) : letI := quiver S; Vertex S ⥤q Q := by
  letI := quiver S
  exact { obj := Subtype.val, map := fun f => f }

def pathInclusion (S : Finset Q) : letI := quiver S; Paths (Vertex S) ⥤ Paths Q := by
  letI := quiver S
  exact Cat.freeMap (inclusion S)

def subsetPrefunctor {S R : Finset Q} (h : S ⊆ R) :
    letI := quiver S
    letI := quiver R
    Vertex S ⥤q Vertex R := by
  letI := quiver S
  letI := quiver R
  exact { obj := fun x => ⟨x.val, h x.property⟩, map := fun f => f }

def subsetFunctor {S R : Finset Q} (h : S ⊆ R) :
    letI := quiver S
    letI := quiver R
    Paths (Vertex S) ⥤ Paths (Vertex R) := by
  letI := quiver S
  letI := quiver R
  exact Cat.freeMap (subsetPrefunctor h)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver
