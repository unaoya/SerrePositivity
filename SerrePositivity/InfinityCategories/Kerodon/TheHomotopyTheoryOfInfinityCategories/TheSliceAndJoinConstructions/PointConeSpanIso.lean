module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeSpanPointAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-!
概要：二つの右余錐辺を貼った三頂点 span を標準ホーンと同定する。
方針：各辺を標準一次元単体へ写し、両 pushout の普遍性を比較する。
規約：共通の始点と両辺を同じ向きで保持する。
使われ方：有限余極限の生成定理を標準的な押し出しの存在へ接続する。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 二つの余錐辺の貼り合わせは、標準の三頂点 span である。 -/
def pointConeSpanIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointConeSpan.{u} ≅ (horn 2 0 : SSet.{u}) := by
  have hp : IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0])
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0])
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₂) := by
    apply horn₂₀.isPushout.of_iso (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).symm (Iso.refl _)
    · rw [Iso.symm_hom, Iso.comp_inv_eq, Iso.refl_hom, Category.id_comp]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl.symm
    · rw [Iso.symm_hom, Iso.comp_inv_eq, Iso.refl_hom, Category.id_comp]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl.symm
    · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id, Iso.inv_hom_id_assoc]
    · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id, Iso.inv_hom_id_assoc]
  exact IsPushout.isoIsPushout _ _ (IsPushout.of_hasPushout _ _) hp

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
