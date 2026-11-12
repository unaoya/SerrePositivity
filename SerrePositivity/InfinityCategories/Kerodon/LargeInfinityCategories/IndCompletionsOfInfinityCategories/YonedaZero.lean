module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.YonedaInitial
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition

/-!
概要：元の零対象を同じ Yoneda 因子化で送り、Indκ の零対象を構成する。
方針：始対象側は filtered 余極限の空形状交換、終対象側は表現可能値と全部分包含で得る。
規約：有限極限交換の未提供入力を使わない。使われ方：F2N-5(a) の pointed 性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の Yoneda 因子化は、元の圏の終対象を Indκ の終対象へ送る。 -/
lemma indYoneda_isTerminal_of_terminal (κ : Cardinal.{u})
    {C : SSet.{u}} [Quasicategory C] {z : C _⦋0⦌} (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up z)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf_isFullyFaithful κ C).reflects_isTerminalVertex
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_vertex_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.representablePresheaf_isTerminal_of_terminal hz

/-- 元の零対象の同じ Yoneda 像は、Indκ 内の実際の零対象。 -/
lemma indYoneda_isZero_of_zero (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    {C : SSet.{u}} [Quasicategory C] {z : C _⦋0⦌} (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up z)) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isInitial_of_initial κ hκ hz.1, indYoneda_isTerminal_of_terminal κ hz.2⟩

/-- 小さい pointed ∞ 圏の Indκ は pointed。安定性と一般の有限極限交換は不要。 -/
lemma ind_hasZeroVertex (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) := by
  obtain ⟨z, hz⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex.exists_zero (X := C)
  exact ⟨_, indYoneda_isZero_of_zero κ hκ hz⟩

/-- 小さい安定 ∞ 圏の Indκ は、正則 κ に対して元の零対象の同じ像を零対象に持つ。 -/
lemma ind_hasZeroVertex_of_stable (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) :=
  ind_hasZeroVertex κ (Cardinal.IsRegular.aleph0_le (Fact.out : κ.IsRegular)) C

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
