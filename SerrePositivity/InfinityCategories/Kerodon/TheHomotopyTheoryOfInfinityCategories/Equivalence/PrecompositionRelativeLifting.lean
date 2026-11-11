module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionCellClosure
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeInternalHomTrivialFibration

/-!
概要：単射の普遍的な同値条件による関手の相対的な持ち上げ。
方針：前合成の全単射の持ち上げを二つの始域の交換で移す。
規約：固定する図式の包含は任意の単射。
使われ方：Kerodon Corollary 4.5.3.31（Tag 01HK）、Theorem 4.6.4.19（Tag 01KU） の固定図式上の比較。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：単射の前合成の同値条件は任意の単射の前合成に対する左持ち上げ性を与える。
方針：同値である前合成の trivial Kan fibration 性と持ち上げ問題の交換を使う。
規約：標的 X のみ quasicategory。i、j は単射。
使われ方：Kerodon §4.5.3（Tag 032Y） の図式を厳密に固定した比較。 -/
lemma IsPrecompositionEquivalence.hasLiftingProperty_pre {A B K L : SSet.{u}}
    {i : A ⟶ B} [Mono i] (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i) (j : K ⟶ L) [Mono j]
    (X : SSet.{u}) [Quasicategory X] : HasLiftingProperty i ((pre j).app X) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre i).app X) := hi.trivialKanFibration_pre X
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hasLiftingProperty_pre_iff_swapped i j X).2
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := (pre i).app X) j inferInstance)

/-- 概要：単射の普遍的な同値に沿う、図式の制限の相対内部 Hom は trivial Kan fibration。
方針：境界との pushout-product が単射の同値条件を持つことと二変数随伴を使う。
規約：固定図式の包含 j は単射、標的 X は quasicategory。
使われ方：Kerodon §4.5.3（Tag 032Y） の同じ固定図式上の自然な同型。 -/
lemma IsPrecompositionEquivalence.trivialKanFibration_relative_pre
    {A B K L : SSet.{u}} {i : A ⟶ B} [Mono i]
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i) (j : K ⟶ L) [Mono j]
    (X : SSet.{u}) [Quasicategory X]
    (sq' : internalHom.PullbackObjObj i ((pre j).app X)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration sq'.π := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i (boundary n).ι
  have : Mono sq.ι := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.mono_pushoutObjObj_ι i (boundary n).ι sq
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  exact (hi.pushoutObjObj (boundary n).ι sq).hasLiftingProperty_pre j X

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
