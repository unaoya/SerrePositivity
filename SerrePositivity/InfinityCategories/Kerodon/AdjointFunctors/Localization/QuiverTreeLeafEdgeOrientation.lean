module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeCollapseGenerators

/-!
# 元の葉の接続辺の向きの回収

概要：元の葉に接する生成辺は元の接続辺そのもので、逆向きの辺は存在しない。
方針：対称生成辺の一意性と二つのコンストラクタの非交差性を使う。
規約：元の生成辺の異種等式を保持する。
使われ方：葉の除去の向きに応じた自然変換。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] {T : WideSubquiver (Quiver.Symmetrify Q)}
  [Quiver.Arborescence T] {S : Finset Q} (D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeafDeletion T S)

lemma LeafDeletion.incoming_eq_positive (g : D.parent ⟶ D.leaf) (hg : D.edge.val = g.toPos)
    {x : Q} (hx : x ∈ S) (f : x ⟶ D.leaf) : x = D.parent ∧ HEq f g := by
  obtain ⟨he, hh⟩ := D.incoming_parent hx f
  subst x
  have hs : f.toPos = g.toPos := (eq_of_heq hh).trans hg
  exact ⟨rfl, heq_of_eq (Sum.inl.inj hs)⟩

lemma LeafDeletion.no_outgoing_positive (g : D.parent ⟶ D.leaf) (hg : D.edge.val = g.toPos)
    {x : Q} (hx : x ∈ S) (f : D.leaf ⟶ x) : False := by
  obtain ⟨he, hh⟩ := D.outgoing_parent hx f
  subst x
  have hs : f.toNeg = g.toPos := (eq_of_heq hh).trans hg
  cases hs

lemma LeafDeletion.outgoing_eq_negative (g : D.leaf ⟶ D.parent) (hg : D.edge.val = g.toNeg)
    {x : Q} (hx : x ∈ S) (f : D.leaf ⟶ x) : x = D.parent ∧ HEq f g := by
  obtain ⟨he, hh⟩ := D.outgoing_parent hx f
  subst x
  have hs : f.toNeg = g.toNeg := (eq_of_heq hh).trans hg
  exact ⟨rfl, heq_of_eq (Sum.inr.inj hs)⟩

lemma LeafDeletion.no_incoming_negative (g : D.leaf ⟶ D.parent) (hg : D.edge.val = g.toNeg)
    {x : Q} (hx : x ∈ S) (f : x ⟶ D.leaf) : False := by
  obtain ⟨he, hh⟩ := D.incoming_parent hx f
  subst x
  have hs : f.toPos = g.toNeg := (eq_of_heq hh).trans hg
  cases hs

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
