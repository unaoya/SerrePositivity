module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FiniteQuiver
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.PathVertices

/-!
# 有限支持を持つ元の射列の有限 quiver への持ち上げ

概要：元の射列の全頂点を含む有限集合に同じ生成辺を持つ射列を作る。
方針：元の射列の長さ零と連結に沿って再帰する。
規約：始点・終点だけでなく射列の内部頂点も含める。
使われ方：元の hammock の有限部分木への因子化。
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

def liftPath {x y : Q} (p : Quiver.Path x y) (hp : pathVertices p ⊆ S) :
    letI := quiver S
    @Quiver.Path (Vertex S) (quiver S) (⟨x, hp (pathVertices_source p)⟩ : Vertex S)
      (⟨y, hp (pathVertices_target p)⟩ : Vertex S) := by
  letI := quiver S
  revert hp
  induction p with
  | nil => intro hp; exact Quiver.Path.nil
  | @cons y z p e ih =>
    intro hp
    have hp' : pathVertices p ⊆ S := by
      intro t ht
      exact hp ((pathVertices_cons p e).symm ▸ Finset.mem_insert_of_mem ht)
    exact (ih hp').cons e

lemma liftPath_projection {x y : Q} (p : Quiver.Path x y) (hp : pathVertices p ⊆ S) :
    letI := quiver S
    (inclusion S).mapPath (liftPath S p hp) = p := by
  let := quiver S
  induction p with
  | nil => rfl
  | cons p e ih =>
    change ((inclusion S).mapPath (liftPath S p _)).cons e = p.cons e
    exact congrArg (fun r : Quiver.Path x _ => r.cons e) (ih _)

end SerrePositivity.EInfinity.Hammock.FiniteQuiver
