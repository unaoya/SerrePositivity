module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverGroupoidThin

/-!
# 元の根付き被覆の自由 groupoid の連結性

概要：元の任意の二頂点の間にはちょうど一つの groupoid の射がある。
方針：根からの実際の対称射列を評価し、薄さと合わせる。
規約：Unique は局所的に選べる定義とし、大域 instance は追加しない。
使われ方：元の被覆の木性と hammock の固定端点。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma root_groupoid_hom_nonempty (x : Vertex A) :
    letI := quiver A
    Nonempty ((Quiver.FreeGroupoid.of (Vertex A)).obj (root A) ⟶
      (Quiver.FreeGroupoid.of (Vertex A)).obj x) := by
  let := quiver A
  obtain ⟨p⟩ := root_connected A x
  exact ⟨(symmetricEvaluation (Q := Vertex A)).map p⟩

lemma groupoid_hom_nonempty :
    letI := quiver A
    ∀ x y : Quiver.FreeGroupoid (Vertex A), Nonempty (x ⟶ y) := by
  let := quiver A
  intro x y
  obtain ⟨f⟩ := root_groupoid_hom_nonempty A x.as
  obtain ⟨g⟩ := root_groupoid_hom_nonempty A y.as
  exact ⟨inv f ≫ g⟩

@[instance_reducible] def groupoidHomUnique :
    letI := quiver A
    ∀ x y : Quiver.FreeGroupoid (Vertex A), Unique (x ⟶ y) := by
  letI := quiver A
  intro x y
  exact { default := (groupoid_hom_nonempty A x y).some,
          uniq := fun f => groupoid_hom_unique A f _ }

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
