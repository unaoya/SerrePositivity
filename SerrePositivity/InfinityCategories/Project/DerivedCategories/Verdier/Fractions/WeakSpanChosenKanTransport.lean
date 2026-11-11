module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.KST.Fibration.GroupoidCompletionKanMaps
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakDenominatorSpanTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Ho

/-! # 元の各 W 辺の選択した span 輸送の厳密 Kan 模型での同値性 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}

/-- cocartesian prism とともに選択された、同じ元の span 族の実輸送。 -/
def weakSpanChosenTransport (x : B.obj _⦋0⦌) (s : B.obj _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x) (B.obj.δ 1 s) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x) (B.obj.δ 0 s) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianTransport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x) s

/-- 追加の輸送や prism を入力せず、選択した元の W 輸送そのものの亜群化は実際の同値。 -/
theorem weakSpanChosenTransport_groupoidCompletion_isQCatEquivalence
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌) (s : B.obj _⦋1⦌)
    (hs : s ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanChosenTransport (i := i) x s)) := by
  obtain ⟨H, h₀, h₁, hb, _hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianTransport_isTransport
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x) s
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakDenominatorSpanTransport_groupoidCompletion_isEquivalence h x s hs
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanChosenTransport (i := i) x s) H h₀ h₁ hb).isQCatEquivalence

/-- 厳密 Kan 模型でも、元の各 W 辺の選択した同じ輸送は実際の同値。 -/
theorem weakSpanChosenKanTransport_isQCatEquivalence
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌) (s : B.obj _⦋1⦌)
    (hs : s ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanChosenTransport (i := i) x s)) :=
  strictKanCompletion_map_isQCatEquivalence_of_groupoidCompletion _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanChosenTransport_groupoidCompletion_isQCatEquivalence h x s hs)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanChosenKanTransport_isQCatEquivalence := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanChosenKanTransport_isQCatEquivalence

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanChosenTransport (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanChosenTransport := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanChosenTransport

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanChosenTransport_groupoidCompletion_isQCatEquivalence := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanChosenTransport_groupoidCompletion_isQCatEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanChosenTransport._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanChosenTransport._proof_1
