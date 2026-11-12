module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TerminalRightFibrationComparison

/-!
概要：底を保つ同じ標準 fiber 比較を通じて、任意の終対象比較の同値性を移す。
方針：全パラメータの実比較を保持し、終対象性と厳密な fiber の比較を使う。
規約：安定性や有限極限を先取りしない。使われ方：一般安定性判定の実錐比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 底を保つ標準 fiber 同値があれば、終対象比較の同じ実区間族も同値。 -/
lemma terminalComparisonIntervalFamily_isQCatEquivalence_of_fiberEquivalence
    {E C B : SSet.{u}} [Quasicategory E] [Quasicategory C] [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (F : E ⟶ C) (q : C ⟶ B) (hF : F ≫ q = p)
    (t : E _⦋0⦌) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex t)
    (hFt : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (F.app (Opposite.op ⦋0⦌) t)) (x : B _⦋0⦌)
    [Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q x)]
    (hk : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q F hF x))
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q x) (SSet.const (F.app (Opposite.op ⦋0⦌) t))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalComparisonIntervalFamily q (F.app (Opposite.op ⦋0⦌) t) x
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp q x) H) := by
  subst p
  let p := F ≫ q
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x
  let k : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q x := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q F rfl x
  have hterm := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise (SSet.const (X := A) t)
    (fun _ ↦ by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant t 0)
      rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero])
  obtain ⟨e⟩ := hterm.nonempty_edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x))
  let HE := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e
  have hα : k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q x = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x ≫ F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι _ _ _ _ _
  have hf : (k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q x) ≫ q = SSet.const x := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  let H₁ : SSet.Homotopy (k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q x)
      (SSet.const (F.app (Opposite.op ⦋0⦌) t)) := {
    h := (k ▷ (Δ[1] : SSet.{u})) ≫ H.h
    h₀ := by rw [SSet.ι₀_comp_assoc, H.h₀]; rfl
    h₁ := by rw [SSet.ι₁_comp_assoc, H.h₁, SSet.comp_const]; rfl
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  let H₂ : SSet.Homotopy (k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q x)
      (SSet.const (F.app (Opposite.op ⦋0⦌) t)) := {
    h := HE.h ≫ F
    h₀ := by rw [← Category.assoc, HE.h₀, ← hα]; rfl
    h₁ := by rw [← Category.assoc, HE.h₁, SSet.const_comp]; rfl
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  have h₁ : k ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalComparisonIntervalFamily q (F.app (Opposite.op ⦋0⦌) t) x
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp q x) H =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalComparisonIntervalFamily q (F.app (Opposite.op ⦋0⦌) t) x
        (k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q x) hf H₁ := by
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.intervalFamilyHomotopy_h_injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy_precomp_h, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalComparisonIntervalFamily_h,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalComparisonIntervalFamily_h]
    simp only [H₁, Category.assoc]
  have h₂ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalComparisonIntervalFamily q (F.app (Opposite.op ⦋0⦌) t) x
        (k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q x) hf H₂ =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalComparisonIntervalFamily p t x (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp p x) HE := by
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.intervalFamilyHomotopy_h_injective
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalComparisonIntervalFamily_h, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalComparisonIntervalFamily_h]
    exact Category.assoc HE.h F q
  obtain ⟨L⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalComparisonIntervalFamily_homotopy q _ hFt x
    (k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q x) hf H₁ H₂
  rw [← h₁, h₂] at L
  have hE := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalComparisonIntervalFamily_isQCatEquivalence p t ht x HE
  exact hk.cancel_left (hE.ofFunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy L).symm)
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
