module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.Finset.Basic

/-!
# 元の射列に現れる有限頂点集合

概要：始点と終点を含む元の射列の全頂点を有限集合にする。
方針：元の Path.toList に終点を加える。
規約：長さ零の元の射列も含む。
使われ方：元の hammock の有限部分木への因子化。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

attribute [local instance] Classical.propDecidable

variable {V : Type u} [Quiver.{v} V]

def pathVertices {x y : V} (p : Quiver.Path x y) : Finset V := by
  classical
  exact insert y p.toList.toFinset

lemma pathVertices_nil (x : V) : pathVertices (Quiver.Path.nil : Quiver.Path x x) = {x} := by
  classical
  simp [pathVertices]

lemma pathVertices_cons {x y z : V} (p : Quiver.Path x y) (e : y ⟶ z) :
    pathVertices (p.cons e) = insert z (pathVertices p) := by
  classical
  simp [pathVertices]

lemma pathVertices_target {x y : V} (p : Quiver.Path x y) : y ∈ pathVertices p := by
  classical
  exact Finset.mem_insert_self _ _

lemma pathVertices_source {x y : V} (p : Quiver.Path x y) : x ∈ pathVertices p := by
  classical
  induction p with
  | nil => simp [pathVertices_nil]
  | cons p e ih => rw [pathVertices_cons]; exact Finset.mem_insert_of_mem ih

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
