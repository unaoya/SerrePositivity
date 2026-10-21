module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverGroupoidFaithful

/-!
# 元の根付き被覆の自由 groupoid の薄さ

概要：被覆の同じ二頂点の間の自由 groupoid の射は一意である。
方針：終点の式で射影を比較し、証明済みの忠実性を適用する。
規約：元の groupoid の全射を対象とし、薄さを入力にしない。
使われ方：被覆の木性と固定端点の hammock の持ち上げ。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma groupoid_hom_unique :
    letI := quiver A
    ∀ {x y : Quiver.FreeGroupoid (Vertex A)} (f g : x ⟶ y), f = g := by
  let := quiver A
  let := groupoidProjection_faithful A
  intro x y f g
  apply (groupoidProjection A).map_injective
  apply (cancel_epi x.as.path).mp
  exact (groupoidProjection_endpoint A f).trans (groupoidProjection_endpoint A g).symm

lemma groupoid_isThin : letI := quiver A; Quiver.IsThin (Quiver.FreeGroupoid (Vertex A)) := by
  let := quiver A
  intro x y
  exact ⟨fun f g => groupoid_hom_unique A f g⟩

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
