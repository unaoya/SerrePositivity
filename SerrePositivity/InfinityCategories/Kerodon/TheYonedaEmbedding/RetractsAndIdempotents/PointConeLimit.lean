module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceIdentityTerminal

/-!
概要：元の一点図式の錐が同じ頂点への定値写像なら、元の錐は極限錐である。
方針：元の図式を固定条件から復元し、保存済みの恒等錐の終対象性を適用する。
規約：点の図式の表示と元の錐の全写像を保持する。
使われ方：元の強い分裂の全錐を始対象の一点へ制限した後の判定。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の一点図式への定値な全錐は、その元の頂点を持つ極限錐。 -/
lemma pointCone_isLimit_of_constant {X : SSet.{u}} [Quasicategory X]
    {p : (Δ[0] : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (x : X _⦋0⦌)
    (hc : c.val = SSet.const x) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
  have hp : p = SSet.yonedaEquiv.symm x := by
    rw [← c.property, hc, SSet.comp_const, SSet.yonedaEquiv_symm_zero]
  subst p
  have he : c = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone x := Subtype.ext hc
  rw [he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceIdentityCone_isTerminalVertex x

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
