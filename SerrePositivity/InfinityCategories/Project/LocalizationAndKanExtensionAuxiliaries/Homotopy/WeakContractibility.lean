module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-!
概要：全境界を充填できる可縮 Kan 複体から弱可縮性への接続。
方針：一点への trivial Kan fibration に逆を作り、弱ホモトピー同値へ移す。
規約：一般の弱可縮な単体集合に全境界の充填を要求するものではない。
使われ方：Quillen A の判定に使う可縮な補助空間と既存 Core の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy

/-- 概要：単体集合の終対象は全境界を充填する。
方針：各標準単体からの一意な射を取る。
規約：選ばれた終対象を使う。
使われ方：弱可縮性と可縮 Kan 複体の接続。 -/
lemma isContractibleKan_terminal : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (⊤_ SSet.{u}) := by
  intro n b
  exact ⟨terminal.from (Δ[n] : SSet.{u}), terminal.hom_ext _ _⟩

/-- 概要：全境界を充填できる単体集合は弱可縮。
方針：Kan 性を導き、点への trivial Kan fibration の明示的な逆を使う。
規約：この十分条件を弱可縮性の定義には使わない。
使われ方：Core の IsContractibleKan から Quillen A の条件への接続。 -/
lemma IsContractibleKan.isWeaklyContractible {K : SSet.{u}} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K := by
  have := h.kanComplex
  have := isContractibleKan_terminal.{u}.kanComplex
  have := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration K).mp h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (terminal.from K)).isWeakHomotopyEquivalence

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan export _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.IsContractibleKan (isWeaklyContractible)


/-- 概要：一点は弱可縮。
方針：全境界の充填による十分性を適用する。
規約：選ばれた終対象の単体集合。
使われ方：弱可縮性の基本例。 -/
lemma isWeaklyContractible_terminal : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (⊤_ SSet.{u}) :=
  isContractibleKan_terminal.isWeaklyContractible

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
