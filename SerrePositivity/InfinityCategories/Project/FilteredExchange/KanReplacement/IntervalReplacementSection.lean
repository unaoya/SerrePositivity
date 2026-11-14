module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalReplacementKanComparison

/-!
概要：区間の path 置換の定値切断と、その弱ホモトピー同値性。
方針：既存の可逆 path の切断を比較同型で送り、射影の自明性で検査する。
規約：終点との合成は元の射に厳密に一致する。
使われ方：元の cospan と path 置換した cospan の自然な比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {X Y : SSet.{u}} [KanComplex Y]

/-- 概要：元の始域から定値 path による置換への切断。
方針：可逆 path の標準切断を区間関手の置換へ送る。
規約：元の射の像の定値 path。使われ方：cospan の比較の第一成分。 -/
def intervalReplacementSection (f : X ⟶ Y) : X ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacement f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection f ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.equivalenceIntervalReplacementIso f).hom

/-- 概要：切断の元の始域への射影は恒等射。
方針：比較同型の第二射影と既存の切断の式を使う。
規約：厳密な等式。使われ方：切断の弱同値性。 -/
lemma intervalReplacementSection_projection (f : X ⟶ Y) :
    intervalReplacementSection f ≫ pullback.snd ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f = 𝟙 X := by
  rw [intervalReplacementSection, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.equivalenceIntervalReplacementIso_snd,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection]

/-- 概要：切断の終点での評価は元の射。
方針：比較同型の終点の式と可逆 path の切断の式を使う。
規約：cospan の自然性はこの等式を使う。使われ方：元の図式を保持する比較。 -/
lemma intervalReplacementSection_endpoint (f : X ⟶ Y) :
    intervalReplacementSection f ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f = f := by
  rw [intervalReplacementSection, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.equivalenceIntervalReplacementIso_endpoint,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_map]

/-- 概要：Kan 複体の定値 path の切断は弱ホモトピー同値。
方針：可逆 path の射影の自明 Kan 性を消去し、比較同型を合成する。
規約：元の f の fibration 性は不要。使われ方：図式の同値の成分。 -/
lemma intervalReplacementSection_isWeakHomotopyEquivalence [KanComplex X] (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (intervalReplacementSection f) := by
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f)).isWeakHomotopyEquivalence
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection f) := by
    apply hp.cancel_right
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id X).isWeakHomotopyEquivalence
  exact hs.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.equivalenceIntervalReplacementIso f)).isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.Project.FilteredExchange
