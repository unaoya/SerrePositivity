module
public import SerrePositivity.InfinityCategories.Stable.TerminalComparisonIntervalFamily
public import SerrePositivity.InfinityCategories.Stable.SliceEvaluationNaturality
public import SerrePositivity.InfinityCategories.F1B.UnitCompositionTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.VertexFiberMapLifting
public import SerrePositivity.InfinityCategories.Derived.RightFibrationTerminalRepresentation

/-!
概要：終対象を持つ right fibration の任意の実比較は、同じ実 fiber を表現する。
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

/-- 両端固定の実区間族は、その円柱写像で一意に決まる。 -/
lemma intervalFamilyHomotopy_h_injective {A B : SSet.{u}} {x y : B _⦋0⦌}
    {f g : A ⟶ intervalMappingSpace x y}
    (h : (intervalFamilyHomotopy f).h = (intervalFamilyHomotopy g).h) : f = g := by
  apply intervalMappingUncurry_injective x y
  apply (cancel_epi (β_ A (Δ[1] : SSet.{u})).hom).1
  exact h

/-- right fibration の終対象への任意の比較からの実区間族は同値。 -/
lemma terminalComparisonIntervalFamily_isQCatEquivalence {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [RightFibration p]
    (t : E _⦋0⦌) (ht : IsTerminalVertex t) (x : B _⦋0⦌)
    (H : SSet.Homotopy (vertexFiberι p x) (SSet.const t)) :
    IsQCatEquivalence (terminalComparisonIntervalFamily p t x (vertexFiberι p x)
      (vertexFiberι_comp p x) H) := by
  let r := sliceOverProjection (SSet.yonedaEquiv.symm t)
  let z := p.app (Opposite.op ⦋0⦌) t
  let rB := sliceOverProjection (SSet.yonedaEquiv.symm z)
  let T := vertexFiber (r ≫ p) x
  let a := vertexFiberι (r ≫ p) x
  let u : T ⟶ vertexFiber p x := vertexFiberMap (r ≫ p) p r rfl x
  let v : T ⟶ vertexFiber rB x := vertexFiberMap (r ≫ p) rB (roofTargetSliceMap p t)
    (roofTargetSliceMap_projection p t) x
  let : TrivialKanFibration r := (isTerminalVertex_iff_trivialKanFibration t).1 ht
  let : TrivialKanFibration u := HomotopyLimits.vertexFiberMap_trivialKanFibration _ _ _ _ x
  let : Quasicategory T := quasicategory_of_innerFibration u
  let := roofTargetSliceMap_trivialKanFibration p t
  let : TrivialKanFibration v := HomotopyLimits.vertexFiberMap_trivialKanFibration _ _ _ _ x
  have hu : IsQCatEquivalence u := isQCatEquivalence_of_trivialKanFibration u
  have hv : IsQCatEquivalence v := isQCatEquivalence_of_trivialKanFibration v
  let b := v ≫ (pinchedHomSliceFiberIso x z).inv
  let w := b ≫ pinchedHomToIntervalMappingSpace x z
  have hw : IsQCatEquivalence w :=
    (hv.comp (qCatEquivalenceOfIso (pinchedHomSliceFiberIso x z).symm).isQCatEquivalence).comp
      (pinchedHomToIntervalMappingSpace_isQCatEquivalence x z)
  have huf : u ≫ vertexFiberι p x = a ≫ r := vertexFiberMap_ι _ _ _ _ x
  have hfp : (u ≫ vertexFiberι p x) ≫ p = SSet.const x := by
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]
  let H₁ : SSet.Homotopy (u ≫ vertexFiberι p x) (SSet.const t) := {
    h := (u ▷ (Δ[1] : SSet.{u})) ≫ H.h
    h₀ := by rw [SSet.ι₀_comp_assoc, H.h₀]; rfl
    h₁ := by rw [SSet.ι₁_comp_assoc, H.h₁, SSet.comp_const]; rfl
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  let H₂ : SSet.Homotopy (u ≫ vertexFiberι p x) (SSet.const t) := {
    h := (functorHomotopyPrecomp (roofSliceEvaluationHomotopy t) a).h
    h₀ := (functorHomotopyPrecomp (roofSliceEvaluationHomotopy t) a).h₀.trans huf.symm
    h₁ := by
      rw [(functorHomotopyPrecomp (roofSliceEvaluationHomotopy t) a).h₁, SSet.comp_const]
      rfl
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  have h₁ : u ≫ terminalComparisonIntervalFamily p t x (vertexFiberι p x)
      (vertexFiberι_comp p x) H = terminalComparisonIntervalFamily p t x
        (u ≫ vertexFiberι p x) hfp H₁ := by
    apply intervalFamilyHomotopy_h_injective
    rw [intervalFamilyHomotopy_precomp_h, terminalComparisonIntervalFamily_h,
      terminalComparisonIntervalFamily_h]
    simp only [H₁, Category.assoc]
  have hb : b ≫ pinchedFamilySlice B x z = a ≫ roofTargetSliceMap p t := by
    change (v ≫ (pinchedHomSliceFiberIso x z).inv) ≫
      (pinchedHomSliceFiberIso x z).hom ≫ vertexFiberι rB x = _
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    exact vertexFiberMap_ι _ _ _ _ x
  have h₂ : terminalComparisonIntervalFamily p t x (u ≫ vertexFiberι p x) hfp H₂ = w := by
    apply intervalFamilyHomotopy_h_injective
    rw [terminalComparisonIntervalFamily_h]
    change (functorHomotopyPrecomp (roofSliceEvaluationHomotopy t) a).h ≫ p = _
    rw [roofSliceEvaluationHomotopy_postcomp_h, ← hb,
      roofSliceEvaluationHomotopy_pinched_h]
  obtain ⟨L⟩ := terminalComparisonIntervalFamily_homotopy p t ht x
    (u ≫ vertexFiberι p x) hfp H₁ H₂
  rw [← h₁, h₂] at L
  exact hu.cancel_left (hw.ofFunctorIso (functorIsoOfSimplicialHomotopy L).symm)
end SerrePositivity.InfinityCategories
