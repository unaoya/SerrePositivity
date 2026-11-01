module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FiniteQuiverPathLift
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FiniteQuiverFaithful

/-!
# 同じ元の端点を持つ有限支持の射列の一意な持ち上げ

概要：元の指定した有限頂点を端点として同じ射列を持ち上げる。
方針：内部の全頂点を含む持ち上げと元の忠実性を使う。
規約：射影後は元の射列へ厳密に戻る。
使われ方：有限支持の行と図式の恒等・合成を検査する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FiniteQuiver
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (S : Finset Q)

def liftArrow (x y : Vertex S) (p : Quiver.Path x.val y.val) (hp : pathVertices p ⊆ S) :
    letI := quiver S
    (Paths.of (Vertex S)).obj x ⟶ (Paths.of (Vertex S)).obj y := by
  letI := quiver S
  exact liftPath S p hp

lemma liftArrow_projection (x y : Vertex S) (p : Quiver.Path x.val y.val)
    (hp : pathVertices p ⊆ S) : letI := quiver S
    (pathInclusion S).map (liftArrow S x y p hp) = p := by
  let := quiver S
  exact liftPath_projection S p hp

lemma liftArrow_unique (x y : Vertex S) (p : Quiver.Path x.val y.val)
    (hp : pathVertices p ⊆ S) : letI := quiver S
    ∀ q : (Paths.of (Vertex S)).obj x ⟶ (Paths.of (Vertex S)).obj y,
      (pathInclusion S).map q = p → liftArrow S x y p hp = q := by
  let := quiver S
  let := pathInclusion_faithful S
  intro q hq
  apply (pathInclusion S).map_injective
  exact (liftArrow_projection S x y p hp).trans hq.symm

end SerrePositivity.EInfinity.Hammock.FiniteQuiver
