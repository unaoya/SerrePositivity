module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PathVertices

/-!
# 有限支持を持つ元の射列の有限 quiver への持ち上げ

概要：元の射列の全頂点を含む有限集合に同じ生成辺を持つ射列を作る。
方針：元の射列の長さ零と連結に沿って再帰する。
規約：始点・終点だけでなく射列の内部頂点も含める。
使われ方：元の hammock の有限部分木への因子化。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiverPathLift
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (S : Finset Q)

def liftPath {x y : Q} (p : Quiver.Path x y) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices p ⊆ S) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    @Quiver.Path (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S) (⟨x, hp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices_source p)⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)
      (⟨y, hp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices_target p)⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  revert hp
  induction p with
  | nil => intro hp; exact Quiver.Path.nil
  | @cons y z p e ih =>
    intro hp
    have hp' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices p ⊆ S := by
      intro t ht
      exact hp ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices_cons p e).symm ▸ Finset.mem_insert_of_mem ht)
    exact (ih hp').cons e

lemma liftPath_projection {x y : Q} (p : Quiver.Path x y) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices p ⊆ S) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.inclusion S).mapPath (liftPath S p hp) = p := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  induction p with
  | nil => rfl
  | cons p e ih =>
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.inclusion S).mapPath (liftPath S p _)).cons e = p.cons e
    exact congrArg (fun r : Quiver.Path x _ => r.cons e) (ih _)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiverPathLift
