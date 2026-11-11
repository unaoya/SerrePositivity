module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarShiftedInclusions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarShiftBlockInclusion

/-!
概要：bar からの全次数 Hom の零を、元の単体からのシフト付き包含で検出する。
方針：各余積列に制限し、実 shift の包含・射影の逆則で元の列を回収する。
規約：閉零射や h 圏への制限を課さず、全次数の元そのものを扱う。
使われ方：Bianchi から得られる曲率の合成零を、bar の無条件 MC に戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgModuleHom_eq_zero_of_comp_shiftIn {M N : _root_.SerrePositivity.DifferentialGraded.RightModule R D} (s : ℤ) {k t : ℤ}
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (_root_.SerrePositivity.DifferentialGraded.shiftModule s M) N).X k) (ht : -s + k = t)
    (hf : _root_.SerrePositivity.DifferentialGraded.compose R (x := M) (y := _root_.SerrePositivity.DifferentialGraded.shiftModule s M) (z := N)
      f (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement R D s M) ht = 0) : f = 0 := by
  have he : _root_.SerrePositivity.DifferentialGraded.compose R (x := _root_.SerrePositivity.DifferentialGraded.shiftModule s M) (y := M) (z := N)
      (_root_.SerrePositivity.DifferentialGraded.compose R (x := M) (y := _root_.SerrePositivity.DifferentialGraded.shiftModule s M) (z := N)
        f (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement R D s M) ht)
      (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement R D s M) (show s + t = k by omega) = f := by
    calc
      _ = _root_.SerrePositivity.DifferentialGraded.compose R (x := _root_.SerrePositivity.DifferentialGraded.shiftModule s M) (y := _root_.SerrePositivity.DifferentialGraded.shiftModule s M) (z := N)
          f (_root_.SerrePositivity.DifferentialGraded.compose R (x := _root_.SerrePositivity.DifferentialGraded.shiftModule s M) (y := M) (z := _root_.SerrePositivity.DifferentialGraded.shiftModule s M)
            (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement R D s M) (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement R D s M)
            (add_neg_cancel s)) (zero_add k) :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := R) (D := RightModule R D)
          (w := _root_.SerrePositivity.DifferentialGraded.shiftModule s M) (x := M) (y := _root_.SerrePositivity.DifferentialGraded.shiftModule s M) (z := N)
          (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement R D s M) (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement R D s M) f
          (add_neg_cancel s) ht (zero_add k)).symm
      _ = f := by rw [_root_.SerrePositivity.DifferentialGraded.moduleShiftOutIn R D s M, _root_.SerrePositivity.DifferentialGraded.compose_unit]

  rw [hf, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose] at he
  exact he.symm

variable {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarHom_eq_zero_of_shiftedInclusions (N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (k : ℤ)
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N)).X k)
    (hf : ∀ s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I,
      compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s)
        (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N)
        f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F s) rfl = 0) : f = 0 := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv R D F N k).injective
  funext s
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv_apply, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv_apply]
  simp only [map_zero]
  apply dgModuleHom_eq_zero_of_comp_shiftIn R D (s.1 : ℤ) _ rfl
  have hs := hf s
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion at hs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right, moduleHomClosedInsertion R D
    (S := ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F s))
    (M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s) (N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) (P := N)] at hs
  have hz := congrArg (fun z => (s.1 : ℤ).negOnePow • z) hs
  simpa only [smul_smul, Int.units_mul_self, one_smul, smul_zero] using hz

end SerrePositivity.InfinityCategories.Project.DerivedCategories
