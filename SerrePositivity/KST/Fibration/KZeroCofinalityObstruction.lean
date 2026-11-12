module
public import SerrePositivity.KST.Fibration.VerdierKZeroSurjectivity
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # 元の Verdier 商辺の三角圏 K₀ の余核としての零次 cofinality 障害 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 同じ完全関手の三角圏 K₀ 作用の余核。完備化後の別の商射には置き換えない。 -/
abbrev stableKZeroCofinalityObstruction {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :=
  TriangulatedK0 (hoFunctor.obj C.obj) ⧸ (stableKZeroMap q).range

/-- 元の Verdier 商射の代数的 K₀ の零次余核は零群。 -/
theorem verdierKZeroCofinalityObstruction_subsingleton {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    Subsingleton (stableKZeroCofinalityObstruction q) := by
  have hr := AddMonoidHom.range_eq_top.mpr (verdierKZeroMap_surjective h)
  unfold stableKZeroCofinalityObstruction
  rw [hr]
  exact QuotientAddGroup.subsingleton_quotient_top

end SerrePositivity.KST.Fibration
