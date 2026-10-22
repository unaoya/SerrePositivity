module

public import SerrePositivity.InfinityCategories.F1B.KanSliceIdentityTerminal

/-!
概要：元の一点図式の錐が同じ頂点への定値写像なら、元の錐は極限錐である。
方針：元の図式を固定条件から復元し、保存済みの恒等錐の終対象性を適用する。
規約：点の図式の表示と元の錐の全写像を保持する。
使われ方：元の強い分裂の全錐を始対象の一点へ制限した後の判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の一点図式への定値な全錐は、その元の頂点を持つ極限錐。 -/
lemma pointCone_isLimit_of_constant {X : SSet.{u}} [Quasicategory X]
    {p : (Δ[0] : SSet.{u}) ⟶ X} (c : JoinCone p) (x : X _⦋0⦌)
    (hc : c.val = SSet.const x) : IsLimitCone c := by
  have hp : p = SSet.yonedaEquiv.symm x := by
    rw [← c.property, hc, SSet.comp_const, SSet.yonedaEquiv_symm_zero]
  subst p
  have he : c = sliceIdentityCone x := Subtype.ext hc
  rw [he]
  exact F1B.kanSliceIdentityCone_isTerminalVertex x

end SerrePositivity.InfinityCategories.F2.Idempotent
