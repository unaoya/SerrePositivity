module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CoreFlag.KanPullbackCofinality
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.KanPullbackFibers
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanFibrationVanishing
public import SerrePositivity.KST.SConstruction.Cofinality.KanPullbackCofinalityInput

/-!
概要：K-cof 所有の一般 Kan 引き戻し共終性入力を長完全列から証明する。
方針：右列の fiber の正次数消滅を基点付き fiber 同型で左列へ渡す。
規約：結論は既存の Prop そのもの。元の第一射影の誘導写像を保持する。
使われ方：Sp-8 (3)、K-cof への供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
open Spectra

/-- K-cof の一般 Kan 引き戻し共終性入力の実証明。 -/
theorem kanPullbackCofinalityInput : SConstruction.Cofinality.KanPullbackCofinalityInput.{u} := by
  intro P X E B _ _ _ _ q s g p h hp hE hB a
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff p).mpr hp
  have : Fibration q := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.pullback_fibration h hp
  have hf (n : ℕ) (hn : 0 < n) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CoreFlag.pullback_positive_fiber_subsingleton q s g p h hE hB a n hn
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.fibration_map_injective_of_fiber_subsingleton q a 1 (by omega) (hf 1 (by omega)), ?_⟩
  intro n hn
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.fibration_map_injective_of_fiber_subsingleton q a n (by omega) (hf n (by omega)), ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.fibration_map_surjective_of_fiber_subsingleton q a k (hf k (by omega))

end SerrePositivity.KST.LocalizingInvariants.CoreFlag
