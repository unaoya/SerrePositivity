module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGradedConjugation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionGradedLifting
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ClosedComposition
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R]
/-- 同じ実斉次射と単位関係の境界原始元の構成。 -/
lemma dgSemifreeShift_gradedHomotopyInverse
    (B : Type v) [DGCategory R B] [Small.{u} B] (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R B) (s : ℤ) :
    ∃ (N : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R B)
      (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R M.val N.val (-s)) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R N.val M.val s),
      _root_.SerrePositivity.DifferentialGraded.differential R f = 0 ∧ _root_.SerrePositivity.DifferentialGraded.differential R g = 0 ∧
      ∃ hM : _root_.SerrePositivity.DifferentialGraded.GradedHom R M.val M.val (-1),
        (_root_.SerrePositivity.DifferentialGraded.moduleHom R B M.val M.val).d (-1) 0 hM =
          _root_.SerrePositivity.DifferentialGraded.compose R g f (neg_add_cancel s) - (_root_.SerrePositivity.DifferentialGraded.unitElement R M.val).val ∧
      ∃ hN : _root_.SerrePositivity.DifferentialGraded.GradedHom R N.val N.val (-1),
        (_root_.SerrePositivity.DifferentialGraded.moduleHom R B N.val N.val).d (-1) 0 hN =
          _root_.SerrePositivity.DifferentialGraded.compose R f g (add_neg_cancel s) - (_root_.SerrePositivity.DifferentialGraded.unitElement R N.val).val := by
  obtain ⟨N, π, σ, ⟨hN⟩, ⟨hS⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeShift_resolution_homotopyInverse R B M s
  let π0 : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.moduleHom R B N.val (_root_.SerrePositivity.DifferentialGraded.shiftModule s M.val)) :=
    _root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R B) _ _ π
  let σ0 : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.moduleHom R B (_root_.SerrePositivity.DifferentialGraded.shiftModule s M.val) N.val) :=
    _root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R B) _ _ σ
  let i : _root_.SerrePositivity.DifferentialGraded.GradedHom R M.val (_root_.SerrePositivity.DifferentialGraded.shiftModule s M.val) (-s) := _root_.SerrePositivity.DifferentialGraded.moduleShiftInElement R B s M.val
  let o : _root_.SerrePositivity.DifferentialGraded.GradedHom R (_root_.SerrePositivity.DifferentialGraded.shiftModule s M.val) M.val s := _root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement R B s M.val
  let f : _root_.SerrePositivity.DifferentialGraded.GradedHom R M.val N.val (-s) := _root_.SerrePositivity.DifferentialGraded.compose R (n := -s) σ0.val i (add_zero _)
  let g : _root_.SerrePositivity.DifferentialGraded.GradedHom R N.val M.val s := _root_.SerrePositivity.DifferentialGraded.compose R (n := s) o π0.val (zero_add _)
  have hi : _root_.SerrePositivity.DifferentialGraded.differential R i = 0 := _root_.SerrePositivity.DifferentialGraded.moduleShiftInElement_d R B s M.val
  have ho : _root_.SerrePositivity.DifferentialGraded.differential R o = 0 := _root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement_d R B s M.val
  have hπ : _root_.SerrePositivity.DifferentialGraded.differential R (D := _root_.SerrePositivity.DifferentialGraded.RightModule R B)
    (x := N.val) (y := _root_.SerrePositivity.DifferentialGraded.shiftModule s M.val) π0.val = 0 := π0.property
  have hσ : _root_.SerrePositivity.DifferentialGraded.differential R (D := _root_.SerrePositivity.DifferentialGraded.RightModule R B)
    (x := _root_.SerrePositivity.DifferentialGraded.shiftModule s M.val) (y := N.val) σ0.val = 0 := σ0.property
  have hf : _root_.SerrePositivity.DifferentialGraded.differential R f = 0 := by
    dsimp only [f]
    erw [differential_compose, hσ, hi, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, zero_add]
  have hg : _root_.SerrePositivity.DifferentialGraded.differential R g = 0 := by
    dsimp only [g]
    erw [differential_compose, ho, hπ, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, zero_add]
  have hN' := hN.property
  change (_root_.SerrePositivity.DifferentialGraded.moduleHom R B N.val N.val).d (-1) 0 hN.val =
    ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R B) _ _ (π ≫ σ)).val : _root_.SerrePositivity.DifferentialGraded.GradedHom R N.val N.val 0) -
      ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R B) _ _ (𝟙 (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N.val))).val :
        _root_.SerrePositivity.DifferentialGraded.GradedHom R N.val N.val 0) at hN'
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_id] at hN'
  have hS' := hS.property
  change (_root_.SerrePositivity.DifferentialGraded.moduleHom R B (_root_.SerrePositivity.DifferentialGraded.shiftModule s M.val) (_root_.SerrePositivity.DifferentialGraded.shiftModule s M.val)).d (-1) 0 hS.val =
    ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R B) _ _ (σ ≫ π)).val :
      _root_.SerrePositivity.DifferentialGraded.GradedHom R (_root_.SerrePositivity.DifferentialGraded.shiftModule s M.val) (_root_.SerrePositivity.DifferentialGraded.shiftModule s M.val) 0) -
      ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R B) _ _
        (𝟙 (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.shiftModule s M.val)))).val :
        _root_.SerrePositivity.DifferentialGraded.GradedHom R (_root_.SerrePositivity.DifferentialGraded.shiftModule s M.val) (_root_.SerrePositivity.DifferentialGraded.shiftModule s M.val) 0) at hS'
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_id] at hS'
  let hM := s.negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R (n := (-1 : ℤ)) o
    (_root_.SerrePositivity.DifferentialGraded.compose R (n := -s - 1) hS.val i (by omega)) (by omega)
  refine ⟨N, f, g, hf, hg, hM, ?_, hN.val, ?_⟩
  · have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedConjugateBoundary_sub_unit R (RightModule R B) s i o hi ho
      (_root_.SerrePositivity.DifferentialGraded.moduleShiftInOut R B s M.val) hS.val (_root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ)) π0.val σ0.val rfl) hS'
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedConjugateComposite] at he
    exact he
  · change _ = _root_.SerrePositivity.DifferentialGraded.compose R (n := (0 : ℤ))
      (_root_.SerrePositivity.DifferentialGraded.compose R (n := -s) σ0.val i (add_zero _))
      (_root_.SerrePositivity.DifferentialGraded.compose R (n := s) o π0.val (zero_add _)) (add_neg_cancel s) - _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedTransferInverseComposite R (RightModule R B) s i o
      (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutIn R B s M.val) π0.val σ0.val]
    exact hN'

end SerrePositivity.InfinityCategories.Project.DerivedCategories
