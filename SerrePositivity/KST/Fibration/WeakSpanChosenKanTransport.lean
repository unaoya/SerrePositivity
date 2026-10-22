module
public import SerrePositivity.KST.Fibration.GroupoidCompletionKanMaps
public import SerrePositivity.KST.Fibration.WeakDenominatorSpanTransport
public import SerrePositivity.InfinityCategories.F1.TransportHo

/-! # 元の各 W 辺の選択した span 輸送の厳密 Kan 模型での同値性 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}

/-- cocartesian prism とともに選択された、同じ元の span 族の実輸送。 -/
def weakSpanChosenTransport (x : B.obj _⦋0⦌) (s : B.obj _⦋1⦌) :
    vertexFiber (markedSpanFamilyProjection B.obj (weakEquivalences i) x) (B.obj.δ 1 s) ⟶
      vertexFiber (markedSpanFamilyProjection B.obj (weakEquivalences i) x) (B.obj.δ 0 s) :=
  cocartesianTransport (markedSpanFamilyProjection B.obj (weakEquivalences i) x) s

/-- 追加の輸送や prism を入力せず、選択した元の W 輸送そのものの亜群化は実際の同値。 -/
theorem weakSpanChosenTransport_groupoidCompletion_isQCatEquivalence
    (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌) (s : B.obj _⦋1⦌)
    (hs : s ∈ weakEquivalences i) :
    IsQCatEquivalence (groupoidCompletionMapOf (weakSpanChosenTransport (i := i) x s)) := by
  obtain ⟨H, h₀, h₁, hb, _hc⟩ := cocartesianTransport_isTransport
    (markedSpanFamilyProjection B.obj (weakEquivalences i) x) s
  exact (weakDenominatorSpanTransport_groupoidCompletion_isEquivalence h x s hs
    (weakSpanChosenTransport (i := i) x s) H h₀ h₁ hb).isQCatEquivalence

/-- 厳密 Kan 模型でも、元の各 W 辺の選択した同じ輸送は実際の同値。 -/
theorem weakSpanChosenKanTransport_isQCatEquivalence
    (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌) (s : B.obj _⦋1⦌)
    (hs : s ∈ weakEquivalences i) :
    IsQCatEquivalence (strictKanCompletion.map (weakSpanChosenTransport (i := i) x s)) :=
  strictKanCompletion_map_isQCatEquivalence_of_groupoidCompletion _
    (weakSpanChosenTransport_groupoidCompletion_isQCatEquivalence h x s hs)

end SerrePositivity.KST.Fibration
