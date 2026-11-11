module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanEquivalenceLiftingFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
概要：終対象の core と、その宇宙持ち上げも実際の終対象。
方針：全境界の一意な充填で Kan 性を得て core の厳密な同型を使う。
規約：終対象の単体集合の選択に依存しない。
使われ方：空の境界上の native Hom の core の初期値。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 単体集合の終対象は、同じ境界充填で Kan 複体。 -/
lemma kanComplex_of_sset_isTerminal {X : SSet.{u}} (h : IsTerminal X) : KanComplex X :=
  (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan X from fun n b ↦ ⟨h.from _, h.hom_ext _ _⟩).kanComplex

/-- 終対象の core は、元の終対象との厳密な同型により終対象。 -/
def quasicategoryCore_isTerminal_of_isTerminal {X : SSet.{u}} (h : IsTerminal X) :
    IsTerminal (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u}) := by
  letI := kanComplex_of_sset_isTerminal h
  exact h.ofIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreIsoOfKan X).symm

/-- 元の終対象を同じ宇宙持ち上げで移した単体集合も終対象。 -/
def uliftSSet_isTerminal_of_isTerminal {X : SSet.{u}} (h : IsTerminal X) :
    IsTerminal ((SSet.uliftFunctor.{v, u}).obj X) := by
  letI : PreservesLimit (Functor.empty.{0} SSet.{u}) (SSet.uliftFunctor.{v, u}) := by
    change PreservesLimit (Functor.empty.{0} SSet.{u})
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) (Type (max u v))).obj
        CategoryTheory.uliftFunctor.{v, u})
    infer_instance
  exact h.isTerminalObj (SSet.uliftFunctor.{v, u})

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
