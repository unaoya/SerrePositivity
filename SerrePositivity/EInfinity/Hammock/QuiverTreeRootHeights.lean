module

public import SerrePositivity.EInfinity.Hammock.QuiverTreeRootVertices

/-!
# 根からの射列の元の頂点と高さ

概要：祖先の高さは終点以下で、同じ高さなら同じ頂点である。
方針：元の木の射列で帰納し、各辺の高さの増加を使う。
規約：元の頂点集合と元の高さを保持する。
使われ方：最大高さの葉を除いた集合の根に関する閉性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.QuiverTree
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T]

lemma rootVertices_height_path {x : T} (p : Quiver.Path (Quiver.root T) x) :
    ∀ {y : Q}, y ∈ treePathVertices T p →
      height T (show T from y) ≤ height T x ∧
        (height T (show T from y) = height T x → y = (show Q from x)) := by
  classical
  induction p with
  | nil =>
    intro y hy
    have he : y = (Quiver.root T : Q) := by simpa [treePathVertices_nil] using hy
    subst y
    exact ⟨le_refl _, fun _ => rfl⟩
  | @cons x y p e ih =>
    intro z hz
    rw [treePathVertices_cons] at hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z
      exact ⟨le_refl _, fun _ => rfl⟩
    · have hle := (ih hz).1
      have hs := height_arrow T e
      exact ⟨by omega, fun he => False.elim (by omega)⟩

lemma rootVertices_height {x y : Q} (h : y ∈ rootVertices T x) :
    height T (show T from y) ≤ height T (show T from x) :=
  (rootVertices_height_path T (rootPath T (show T from x)) h).1

lemma rootVertices_eq_of_height_mem {x y : Q} (h : y ∈ rootVertices T x)
    (he : height T (show T from y) = height T (show T from x)) : y = x :=
  (rootVertices_height_path T (rootPath T (show T from x)) h).2 he

end SerrePositivity.EInfinity.Hammock.QuiverTree
