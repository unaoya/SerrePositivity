module
public import SerrePositivity.InfinityCategories.Derived.DGGradedConjugation
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionGradedLifting
public import SerrePositivity.DifferentialGraded.Module.ShiftUnitDifferential
public import SerrePositivity.InfinityCategories.DGNerve.ClosedComposition
/-!
概要：shift の半自由分解から、実斉次閉射と両単位との差の境界原始元を構成する。
方針：同じ Leibniz 式、実単位則と半自由分解のホモトピー逆を使う。
規約：全 Hom の実 cochain を保持する。使われ方：一般 Morita の全高次 Hom の検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R]
/-- 同じ実斉次射と単位関係の境界原始元の構成。 -/
lemma dgSemifreeShift_gradedHomotopyInverse
    (B : Type v) [DGCategory R B] [Small.{u} B] (M : SemifreeDGModules R B) (s : ℤ) :
    ∃ (N : SemifreeDGModules R B)
      (f : GradedHom R M.val N.val (-s)) (g : GradedHom R N.val M.val s),
      differential R f = 0 ∧ differential R g = 0 ∧
      ∃ hM : GradedHom R M.val M.val (-1),
        (moduleHom R B M.val M.val).d (-1) 0 hM =
          compose R g f (neg_add_cancel s) - (unitElement R M.val).val ∧
      ∃ hN : GradedHom R N.val N.val (-1),
        (moduleHom R B N.val N.val).d (-1) 0 hN =
          compose R f g (add_neg_cancel s) - (unitElement R N.val).val := by
  obtain ⟨N, π, σ, ⟨hN⟩, ⟨hS⟩⟩ := dgSemifreeShift_resolution_homotopyInverse R B M s
  let π0 : zeroCycles (moduleHom R B N.val (shiftModule s M.val)) :=
    closedHomEquiv R (RightModule R B) _ _ π
  let σ0 : zeroCycles (moduleHom R B (shiftModule s M.val) N.val) :=
    closedHomEquiv R (RightModule R B) _ _ σ
  let i : GradedHom R M.val (shiftModule s M.val) (-s) := moduleShiftInElement R B s M.val
  let o : GradedHom R (shiftModule s M.val) M.val s := moduleShiftOutElement R B s M.val
  let f : GradedHom R M.val N.val (-s) := compose R (n := -s) σ0.val i (add_zero _)
  let g : GradedHom R N.val M.val s := compose R (n := s) o π0.val (zero_add _)
  have hi : differential R i = 0 := moduleShiftInElement_d R B s M.val
  have ho : differential R o = 0 := moduleShiftOutElement_d R B s M.val
  have hπ : differential R (D := RightModule R B)
    (x := N.val) (y := shiftModule s M.val) π0.val = 0 := π0.property
  have hσ : differential R (D := RightModule R B)
    (x := shiftModule s M.val) (y := N.val) σ0.val = 0 := σ0.property
  have hf : differential R f = 0 := by
    dsimp only [f]
    erw [differential_compose, hσ, hi, zero_compose, compose_zero, smul_zero, zero_add]
  have hg : differential R g = 0 := by
    dsimp only [g]
    erw [differential_compose, ho, hπ, zero_compose, compose_zero, smul_zero, zero_add]
  have hN' := hN.property
  change (moduleHom R B N.val N.val).d (-1) 0 hN.val =
    ((closedHomEquiv R (RightModule R B) _ _ (π ≫ σ)).val : GradedHom R N.val N.val 0) -
      ((closedHomEquiv R (RightModule R B) _ _ (𝟙 (ForgetEnrichment.of (Complex R) N.val))).val :
        GradedHom R N.val N.val 0) at hN'
  rw [HomotopyComparison.closedHom_comp, HomotopyComparison.closedHom_id] at hN'
  have hS' := hS.property
  change (moduleHom R B (shiftModule s M.val) (shiftModule s M.val)).d (-1) 0 hS.val =
    ((closedHomEquiv R (RightModule R B) _ _ (σ ≫ π)).val :
      GradedHom R (shiftModule s M.val) (shiftModule s M.val) 0) -
      ((closedHomEquiv R (RightModule R B) _ _
        (𝟙 (ForgetEnrichment.of (Complex R) (shiftModule s M.val)))).val :
        GradedHom R (shiftModule s M.val) (shiftModule s M.val) 0) at hS'
  rw [HomotopyComparison.closedHom_comp, HomotopyComparison.closedHom_id] at hS'
  let hM := s.negOnePow • compose R (n := (-1 : ℤ)) o
    (compose R (n := -s - 1) hS.val i (by omega)) (by omega)
  refine ⟨N, f, g, hf, hg, hM, ?_, hN.val, ?_⟩
  · have he := dgGradedConjugateBoundary_sub_unit R (RightModule R B) s i o hi ho
      (moduleShiftInOut R B s M.val) hS.val (compose R (n := (0 : ℤ)) π0.val σ0.val rfl) hS'
    rw [dgGradedConjugateComposite] at he
    exact he
  · change _ = compose R (n := (0 : ℤ))
      (compose R (n := -s) σ0.val i (add_zero _))
      (compose R (n := s) o π0.val (zero_add _)) (add_neg_cancel s) - _
    rw [dgGradedTransferInverseComposite R (RightModule R B) s i o
      (moduleShiftOutIn R B s M.val) π0.val σ0.val]
    exact hN'

end SerrePositivity.InfinityCategories
