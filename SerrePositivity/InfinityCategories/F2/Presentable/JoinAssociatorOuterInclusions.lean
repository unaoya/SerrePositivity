module

public import SerrePositivity.InfinityCategories.Core.JoinAssociatorBoundary
public import SerrePositivity.InfinityCategories.Core.JoinAssociatorFactors

/-!
概要：join の逆結合同型と左端の包含・自然性を比較する。
方針：公開された結合同型の順方向の式を同型で打ち消す。
規約：全射の等式を使い、単体の実装を複製しない。
使われ方：二重 slice の組み替えと余極限の対象上への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：逆結合同型は左端の因子の包含を保つ。
方針：順方向の左包含公式を打ち消す。
規約：三因子は任意。
使われ方：二重 slice の固定図式。 -/
lemma joinAssociator_leftmost_inv (K L M : SSet.{u}) :
    joinInl K (join L M) ≫ (stableJoinAssociator K L M).inv =
      joinInl K L ≫ joinInl (join K L) M := by
  apply (cancel_mono (stableJoinAssociator K L M).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    stableJoinAssociator_inl, joinInl_joinMap, Category.id_comp]

/-- 概要：逆結合同型も各因子の射に自然。
方針：順方向の自然性を両結合同型で打ち消す。
規約：任意の全単体集合の射に対する等式。
使われ方：二重 slice 比較の任意パラメーターへの自然性。 -/
lemma joinAssociator_inv_naturality {K K' L L' M M' : SSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M') :
    joinMap f (joinMap g h) ≫ (stableJoinAssociator K' L' M').inv =
      (stableJoinAssociator K L M).inv ≫ joinMap (joinMap f g) h := by
  apply (cancel_epi (stableJoinAssociator K L M).hom).mp
  rw [← Category.assoc, ← stableJoinAssociator_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.F2.Presentable
