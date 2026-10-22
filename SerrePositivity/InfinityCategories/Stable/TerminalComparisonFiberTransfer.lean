module
public import SerrePositivity.InfinityCategories.Stable.TerminalRightFibrationComparison

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
namespace SerrePositivity.InfinityCategories

/-- 底を保つ標準 fiber 同値があれば、終対象比較の同じ実区間族も同値。 -/
lemma terminalComparisonIntervalFamily_isQCatEquivalence_of_fiberEquivalence
    {E C B : SSet.{u}} [Quasicategory E] [Quasicategory C] [Quasicategory B]
    (p : E ⟶ B) [RightFibration p] (F : E ⟶ C) (q : C ⟶ B) (hF : F ≫ q = p)
    (t : E _⦋0⦌) (ht : IsTerminalVertex t)
    (hFt : IsTerminalVertex (F.app (Opposite.op ⦋0⦌) t)) (x : B _⦋0⦌)
    [Quasicategory (vertexFiber q x)]
    (hk : IsQCatEquivalence (vertexFiberMap p q F hF x))
    (H : SSet.Homotopy (vertexFiberι q x) (SSet.const (F.app (Opposite.op ⦋0⦌) t))) :
    IsQCatEquivalence (terminalComparisonIntervalFamily q (F.app (Opposite.op ⦋0⦌) t) x
      (vertexFiberι q x) (vertexFiberι_comp q x) H) := by
  subst p
  let p := F ≫ q
  let A := vertexFiber p x
  let k : A ⟶ vertexFiber q x := vertexFiberMap p q F rfl x
  have hterm := isTerminalVertex_functorVertex_of_pointwise (SSet.const (X := A) t)
    (fun _ ↦ by
      change IsTerminalVertex (PinchedHom.constant t 0)
      rwa [pinchedConstant_zero])
  obtain ⟨e⟩ := hterm.nonempty_edge (functorVertex (vertexFiberι p x))
  let HE := simplicialHomotopyOfFunctorEdge e
  have hα : k ≫ vertexFiberι q x = vertexFiberι p x ≫ F := vertexFiberMap_ι _ _ _ _ _
  have hf : (k ≫ vertexFiberι q x) ≫ q = SSet.const x := by
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]
  let H₁ : SSet.Homotopy (k ≫ vertexFiberι q x)
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
  let H₂ : SSet.Homotopy (k ≫ vertexFiberι q x)
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
  have h₁ : k ≫ terminalComparisonIntervalFamily q (F.app (Opposite.op ⦋0⦌) t) x
      (vertexFiberι q x) (vertexFiberι_comp q x) H =
      terminalComparisonIntervalFamily q (F.app (Opposite.op ⦋0⦌) t) x
        (k ≫ vertexFiberι q x) hf H₁ := by
    apply intervalFamilyHomotopy_h_injective
    rw [intervalFamilyHomotopy_precomp_h, terminalComparisonIntervalFamily_h,
      terminalComparisonIntervalFamily_h]
    simp only [H₁, Category.assoc]
  have h₂ : terminalComparisonIntervalFamily q (F.app (Opposite.op ⦋0⦌) t) x
        (k ≫ vertexFiberι q x) hf H₂ =
      terminalComparisonIntervalFamily p t x (vertexFiberι p x) (vertexFiberι_comp p x) HE := by
    apply intervalFamilyHomotopy_h_injective
    rw [terminalComparisonIntervalFamily_h, terminalComparisonIntervalFamily_h]
    exact Category.assoc HE.h F q
  obtain ⟨L⟩ := terminalComparisonIntervalFamily_homotopy q _ hFt x
    (k ≫ vertexFiberι q x) hf H₁ H₂
  rw [← h₁, h₂] at L
  have hE := terminalComparisonIntervalFamily_isQCatEquivalence p t ht x HE
  exact hk.cancel_left (hE.ofFunctorIso (functorIsoOfSimplicialHomotopy L).symm)
end SerrePositivity.InfinityCategories
