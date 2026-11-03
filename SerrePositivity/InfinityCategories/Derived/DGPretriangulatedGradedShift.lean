module
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulated
public import SerrePositivity.InfinityCategories.Derived.DGGradedConjugation
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.InfinityCategories.DGNerve.ClosedComposition
public import SerrePositivity.InfinityCategories.DGNerve.FunctorMapping

/-! # 前三角 dg 圏の斉次 shift 証人

shifted representable の K(C) における表現可能性から閉斉次射を作り、
全次数 Yoneda 同型で元の dg 圏へ戻す。片側の単位関係の境界原始元も保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

/-- 前三角性は各次数の閉斉次射と、片側の単位との差の境界原始元を与える。 -/
lemma dgPretriangulated_gradedShiftWitness [IsDGPretriangulated R C] (x : C) (s : ℤ) :
    ∃ (w : C) (f : GradedHom R x w (-s)) (g : GradedHom R w x s),
      differential R f = 0 ∧ differential R g = 0 ∧
      ∃ h : GradedHom R x x (-1), (homObject R C x x).d (-1) 0 h =
        compose R g f (neg_add_cancel s) - (unitElement R x).val := by
  let M := representable R x
  let K := moduleToHomotopy R C
  have hshift := dgModuleHomotopyProperty_shift R C (dgRepresentableHomotopyProperty R C)
    (ForgetEnrichment.of (Complex R) M) s (dgHomotopyRepresentable_representable R C x)
  obtain ⟨w, ⟨e⟩⟩ := (dgRepresentableHomotopyProperty_iff R C _).1 hshift
  obtain ⟨σ, hσ⟩ := K.map_surjective e.hom
  obtain ⟨π, hπ⟩ := K.map_surjective e.inv
  obtain ⟨hS⟩ := (moduleToHomotopy_map_eq_iff R C (σ ≫ π) (𝟙 _)).1 (by
    rw [K.map_comp, hσ, hπ, e.hom_inv_id, K.map_id])
  let π0 : zeroCycles (moduleHom R C (representable R w) (shiftModule s M)) :=
    closedHomEquiv R (RightModule R C) _ _ π
  let σ0 : zeroCycles (moduleHom R C (shiftModule s M) (representable R w)) :=
    closedHomEquiv R (RightModule R C) _ _ σ
  let i : GradedHom R M (shiftModule s M) (-s) := moduleShiftInElement R C s M
  let o : GradedHom R (shiftModule s M) M s := moduleShiftOutElement R C s M
  let fM := compose R (n := -s) σ0.val i (add_zero _)
  let gM := compose R (n := s) o π0.val (zero_add _)
  have hi : differential R i = 0 := moduleShiftInElement_d R C s M
  have ho : differential R o = 0 := moduleShiftOutElement_d R C s M
  have hσ0 : differential R (D := RightModule R C) (x := shiftModule s M)
      (y := representable R w) σ0.val = 0 := σ0.property
  have hπ0 : differential R (D := RightModule R C) (x := representable R w)
      (y := shiftModule s M) π0.val = 0 := π0.property
  have hfM : differential R fM = 0 := by
    dsimp only [fM]
    erw [differential_compose, hσ0, hi, zero_compose, compose_zero, smul_zero, zero_add]
  have hgM : differential R gM = 0 := by
    dsimp only [gM]
    erw [differential_compose, ho, hπ0, zero_compose, compose_zero, smul_zero, zero_add]
  have hS' := hS.property
  change (moduleHom R C (shiftModule s M) (shiftModule s M)).d (-1) 0 hS.val =
    ((closedHomEquiv R (RightModule R C)
      (ForgetEnrichment.of (Complex R) (shiftModule s M))
      (ForgetEnrichment.of (Complex R) (shiftModule s M)) (σ ≫ π)).val :
        GradedHom R (shiftModule s M) (shiftModule s M) 0) -
    ((closedHomEquiv R (RightModule R C)
      (ForgetEnrichment.of (Complex R) (shiftModule s M))
      (ForgetEnrichment.of (Complex R) (shiftModule s M)) (𝟙 _)).val :
        GradedHom R (shiftModule s M) (shiftModule s M) 0) at hS'
  rw [HomotopyComparison.closedHom_comp, HomotopyComparison.closedHom_id] at hS'
  let hM := s.negOnePow • compose R (n := (-1 : ℤ)) o
    (compose R (n := -s - 1) hS.val i (by omega)) (by omega)
  have hhM : differential R hM =
      compose R gM fM (neg_add_cancel s) - (unitElement R M).val := by
    have he := dgGradedConjugateBoundary_sub_unit R (RightModule R C) s i o hi ho
      (moduleShiftInOut R C s M) hS.val (compose R π0.val σ0.val rfl) hS'
    rw [dgGradedConjugateComposite] at he
    exact he
  -- 全次数 Yoneda 同型で斉次射と境界関係を C へ戻す。
  let Y := dgYoneda R C
  letI (a b : C) : IsIso (Y.map a b) := by
    change IsIso (dgYonedaIso R a (representable R b)).inv
    infer_instance
  let f : GradedHom R x w (-s) := (inv (Y.map x w)).f (-s) fM
  let g : GradedHom R w x s := (inv (Y.map w x)).f s gM
  let h : GradedHom R x x (-1) := (inv (Y.map x x)).f (-1) hM
  have hf : (Y.map x w).f (-s) f = fM := by
    exact ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom (IsIso.inv_hom_id (Y.map x w)) (-s)) _
  have hg : (Y.map w x).f s g = gM := by
    exact ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom (IsIso.inv_hom_id (Y.map w x)) s) _
  have hh : (Y.map x x).f (-1) h = hM := by
    exact ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom (IsIso.inv_hom_id (Y.map x x)) (-1)) _
  refine ⟨w, f, g, ?_, ?_, h, ?_⟩
  · apply (ModuleCat.mono_iff_injective ((Y.map x w).f (-s + 1))).1 inferInstance
    rw [map_differential, hf, map_zero]
    exact hfM
  · apply (ModuleCat.mono_iff_injective ((Y.map w x).f (s + 1))).1 inferInstance
    rw [map_differential, hg, map_zero]
    exact hgM
  · apply (ModuleCat.mono_iff_injective ((Y.map x x).f 0)).1 inferInstance
    change (Y.map x x).f 0 (differential R h) = _
    have hc := ConcreteCategory.congr_hom ((Y.map x x).comm (-1) 0) h
    change differential R ((Y.map x x).f (-1) h) = (Y.map x x).f 0 (differential R h) at hc
    rw [← hc, hh, map_sub, DGNerve.map_compose, Y.map_unitElement R, hf, hg]
    exact hhM

end SerrePositivity.InfinityCategories
