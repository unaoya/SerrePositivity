module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalSubcomplexRealization
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
概要：小さい終頂点付き部分複体の同じ実現空間と二つの射影。
方針：既存の実現空間を特殊化し、包含順の nerve への trivial Kan 射影を再利用する。
規約：元の単体集合の quasicategory 性を実現空間の仮定にしない。
使われ方：coslice の有限余錐を作って値写像の cofinal 性を検出する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) (X : SSet.{u})

/-- 同じ部分複体の全鎖を実現する空間。 -/
abbrev terminalSubcomplexCarrier : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier (fun A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamily κ X (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexPredicate X) => A.val)
    (fun A => (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexChosenVertex κ X A).val)).toSSet

/-- 元の単体集合への同じ値写像。 -/
def terminalSubcomplexCarrierValue : terminalSubcomplexCarrier κ X ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierValue _ _

/-- 元の包含順への同じ射影。 -/
def terminalSubcomplexCarrierProjection : terminalSubcomplexCarrier κ X ⟶
    nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamily κ X (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexPredicate X)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection _ _

instance terminalSubcomplexCarrierProjection_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (terminalSubcomplexCarrierProjection κ X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection_trivialKanFibration
    (fun A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallSubcomplexFamily κ X (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.terminalSubcomplexPredicate X) => A.val) (fun _ _ h => h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexChosenVertex κ X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexChosenVertex_terminal κ X)

instance terminalSubcomplexCarrier_quasicategory : Quasicategory (terminalSubcomplexCarrier κ X) :=
  quasicategory_of_innerFibration (terminalSubcomplexCarrierProjection κ X)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
