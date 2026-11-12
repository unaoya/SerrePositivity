module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGradedConjugation
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ClosedComposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FunctorMapping

/-! # 前三角 dg 圏の斉次 shift 証人

shifted representable の K(C) における表現可能性から閉斉次射を作り、
全次数 Yoneda 同型で元の dg 圏へ戻す。片側の単位関係の境界原始元も保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]

/-- 前三角性は各次数の閉斉次射と、片側の単位との差の境界原始元を与える。 -/
lemma dgPretriangulated_gradedShiftWitness [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C] (x : C) (s : ℤ) :
    ∃ (w : C) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x w (-s)) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R w x s),
      _root_.SerrePositivity.DifferentialGraded.differential R f = 0 ∧ _root_.SerrePositivity.DifferentialGraded.differential R g = 0 ∧
      ∃ h : _root_.SerrePositivity.DifferentialGraded.GradedHom R x x (-1), (_root_.SerrePositivity.DifferentialGraded.homObject R C x x).d (-1) 0 h =
        _root_.SerrePositivity.DifferentialGraded.compose R g f (neg_add_cancel s) - (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val := by
  let M := _root_.SerrePositivity.DifferentialGraded.representable R x
  let K := _root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R C
  have hshift := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty_shift R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty R C)
    (ForgetEnrichment.of (Complex R) M) s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable_representable R C x)
  obtain ⟨w, ⟨e⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R C _).1 hshift
  obtain ⟨σ, hσ⟩ := K.map_surjective e.hom
  obtain ⟨π, hπ⟩ := K.map_surjective e.inv
  obtain ⟨hS⟩ := (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy_map_eq_iff R C (σ ≫ π) (𝟙 _)).1 (by
    rw [K.map_comp, hσ, hπ, e.hom_inv_id, K.map_id])
  let π0 : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.moduleHom R C (_root_.SerrePositivity.DifferentialGraded.representable R w) (_root_.SerrePositivity.DifferentialGraded.shiftModule s M)) :=
    _root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R C) _ _ π
  let σ0 : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.moduleHom R C (_root_.SerrePositivity.DifferentialGraded.shiftModule s M) (_root_.SerrePositivity.DifferentialGraded.representable R w)) :=
    _root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R C) _ _ σ
  let i : _root_.SerrePositivity.DifferentialGraded.GradedHom R M (_root_.SerrePositivity.DifferentialGraded.shiftModule s M) (-s) := _root_.SerrePositivity.DifferentialGraded.moduleShiftInElement R C s M
  let o : _root_.SerrePositivity.DifferentialGraded.GradedHom R (_root_.SerrePositivity.DifferentialGraded.shiftModule s M) M s := _root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement R C s M
  let fM := _root_.SerrePositivity.DifferentialGraded.compose R (n := -s) σ0.val i (add_zero _)
  let gM := _root_.SerrePositivity.DifferentialGraded.compose R (n := s) o π0.val (zero_add _)
  have hi : _root_.SerrePositivity.DifferentialGraded.differential R i = 0 := _root_.SerrePositivity.DifferentialGraded.moduleShiftInElement_d R C s M
  have ho : _root_.SerrePositivity.DifferentialGraded.differential R o = 0 := _root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement_d R C s M
  have hσ0 : _root_.SerrePositivity.DifferentialGraded.differential R (D := _root_.SerrePositivity.DifferentialGraded.RightModule R C) (x := _root_.SerrePositivity.DifferentialGraded.shiftModule s M)
      (y := _root_.SerrePositivity.DifferentialGraded.representable R w) σ0.val = 0 := σ0.property
  have hπ0 : _root_.SerrePositivity.DifferentialGraded.differential R (D := _root_.SerrePositivity.DifferentialGraded.RightModule R C) (x := _root_.SerrePositivity.DifferentialGraded.representable R w)
      (y := _root_.SerrePositivity.DifferentialGraded.shiftModule s M) π0.val = 0 := π0.property
  have hfM : _root_.SerrePositivity.DifferentialGraded.differential R fM = 0 := by
    dsimp only [fM]
    erw [differential_compose, hσ0, hi, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, zero_add]
  have hgM : _root_.SerrePositivity.DifferentialGraded.differential R gM = 0 := by
    dsimp only [gM]
    erw [differential_compose, ho, hπ0, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, zero_add]
  have hS' := hS.property
  change (_root_.SerrePositivity.DifferentialGraded.moduleHom R C (_root_.SerrePositivity.DifferentialGraded.shiftModule s M) (_root_.SerrePositivity.DifferentialGraded.shiftModule s M)).d (-1) 0 hS.val =
    ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R C)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.shiftModule s M))
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.shiftModule s M)) (σ ≫ π)).val :
        _root_.SerrePositivity.DifferentialGraded.GradedHom R (_root_.SerrePositivity.DifferentialGraded.shiftModule s M) (_root_.SerrePositivity.DifferentialGraded.shiftModule s M) 0) -
    ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R C)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.shiftModule s M))
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.shiftModule s M)) (𝟙 _)).val :
        _root_.SerrePositivity.DifferentialGraded.GradedHom R (_root_.SerrePositivity.DifferentialGraded.shiftModule s M) (_root_.SerrePositivity.DifferentialGraded.shiftModule s M) 0) at hS'
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_id] at hS'
  let hM := s.negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R (n := (-1 : ℤ)) o
    (_root_.SerrePositivity.DifferentialGraded.compose R (n := -s - 1) hS.val i (by omega)) (by omega)
  have hhM : _root_.SerrePositivity.DifferentialGraded.differential R hM =
      _root_.SerrePositivity.DifferentialGraded.compose R gM fM (neg_add_cancel s) - (_root_.SerrePositivity.DifferentialGraded.unitElement R M).val := by
    have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedConjugateBoundary_sub_unit R (RightModule R C) s i o hi ho
      (_root_.SerrePositivity.DifferentialGraded.moduleShiftInOut R C s M) hS.val (_root_.SerrePositivity.DifferentialGraded.compose R π0.val σ0.val rfl) hS'
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedConjugateComposite] at he
    exact he
  -- 全次数 Yoneda 同型で斉次射と境界関係を C へ戻す。
  let Y := _root_.SerrePositivity.DifferentialGraded.dgYoneda R C
  letI (a b : C) : IsIso (Y.map a b) := by
    change IsIso (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R a (_root_.SerrePositivity.DifferentialGraded.representable R b)).inv
    infer_instance
  let f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x w (-s) := (inv (Y.map x w)).f (-s) fM
  let g : GradedHom R w x s := (inv (Y.map w x)).f s gM
  let h : _root_.SerrePositivity.DifferentialGraded.GradedHom R x x (-1) := (inv (Y.map x x)).f (-1) hM
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
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential, hf, map_zero]
    exact hfM
  · apply (ModuleCat.mono_iff_injective ((Y.map w x).f (s + 1))).1 inferInstance
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential, hg, map_zero]
    exact hgM
  · apply (ModuleCat.mono_iff_injective ((Y.map x x).f 0)).1 inferInstance
    change (Y.map x x).f 0 (_root_.SerrePositivity.DifferentialGraded.differential R h) = _
    have hc := ConcreteCategory.congr_hom ((Y.map x x).comm (-1) 0) h
    change _root_.SerrePositivity.DifferentialGraded.differential R ((Y.map x x).f (-1) h) = (Y.map x x).f 0 (_root_.SerrePositivity.DifferentialGraded.differential R h) at hc
    rw [← hc, hh, map_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose, Y.map_unitElement R, hf, hg]
    exact hhM

end SerrePositivity.InfinityCategories.Project.DerivedCategories
