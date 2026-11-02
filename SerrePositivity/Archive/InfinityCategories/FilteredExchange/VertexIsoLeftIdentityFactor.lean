module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoIdentityFactor

/-!
概要：元の指定頂点比較の左恒等因子を、元の頂点同定を保って除去する。
方針：元の頂点同定と恒等比較の HEq を消去する。
規約：右因子の指定値を保持。使われ方：選択済み普遍輸送の自己比較因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 左因子が同じ実終点の恒等比較なら、元の右因子の指定値だけが残る。 -/
lemma vertexIso_trans_heq_of_left_refl {X : SSet.{u}} {a b c : X _⦋0⦌}
    (A : VertexIso a b) (B : VertexIso b c) (hab : a = b)
    (hA : HEq A (Iso.refl (SSet.HomotopyCategory.mk b))) : HEq (A ≪≫ B) B := by
  subst b
  cases eq_of_heq hA
  simp only [Iso.refl_trans]
  rfl

end SerrePositivity.InfinityCategories.F2
