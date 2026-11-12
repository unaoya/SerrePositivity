module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.WeakContractibility
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationContractible

/-!
概要：Kan 複体での弱可縮性は全境界の充填と同値。
方針：一点への弱同値を Kan 複体間の Whitehead 判定に渡し、可縮 Kan 性を移す。
規約：元の Kan 性は必須。一般の弱可縮な単体集合には適用しない。
使われ方：Quillen A の十分性を right fibration の頂点 fiber へ還元した後の判定。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-- 概要：弱可縮な Kan 複体は全境界を充填する。
方針：一点への射のホモトピー同値で可縮 Kan 性を戻す。
規約：Kan 性を明示する。
使われ方：弱可縮な頂点 fiber から trivial Kan fibration 性を得る。 -/
lemma IsWeaklyContractible.isContractibleKan {K : SSet.{u}} [KanComplex K]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K := by
  have := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.isContractibleKan_terminal.{u}.kanComplex
  exact (h.isSimplicialHomotopyEquivalence).isContractibleKan_iff.mpr _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.isContractibleKan_terminal

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible export _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.IsWeaklyContractible (isContractibleKan)


/-- 概要：Kan 複体で弱可縮性と全境界の充填は同値。
方針：Whitehead 判定による必要性と既存の十分性を合わせる。
規約：弱可縮性の定義そのものは変更しない。
使われ方：Quillen A の弱い条件を Kan fiber 内でだけ強い充填条件へ移す。 -/
lemma isWeaklyContractible_iff_isContractibleKan {K : SSet.{u}} [KanComplex K] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible K ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K :=
  ⟨IsWeaklyContractible.isContractibleKan, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.IsContractibleKan.isWeaklyContractible⟩

/-- 概要：right fibration の全ての頂点 fiber が弱可縮なら trivial Kan fibration。
方針：各 fiber の Kan 性により弱可縮性を全境界充填へ移して Core の判定を使う。
規約：底の quasicategory 性は不要。
使われ方：Quillen A の right fibration への還元の最終段階。 -/
lemma rightFibration_trivialKanFibration_of_weaklyContractible_fibers {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p]
    (hc : ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_trivialKanFibration_of_contractible_fibers p
  intro b
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex p b
  exact (hc b).isContractibleKan

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
