module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarShiftedInclusions
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarShiftBlockInclusion

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgModuleHom_eq_zero_of_comp_shiftIn {M N : RightModule R D} (s : ℤ) {k t : ℤ}
    (f : (moduleHom R D (shiftModule s M) N).X k) (ht : -s + k = t)
    (hf : compose R (x := M) (y := shiftModule s M) (z := N)
      f (moduleShiftInElement R D s M) ht = 0) : f = 0 := by
  have he : compose R (x := shiftModule s M) (y := M) (z := N)
      (compose R (x := M) (y := shiftModule s M) (z := N)
        f (moduleShiftInElement R D s M) ht)
      (moduleShiftOutElement R D s M) (show s + t = k by omega) = f := by
    calc
      _ = compose R (x := shiftModule s M) (y := shiftModule s M) (z := N)
          f (compose R (x := shiftModule s M) (y := M) (z := shiftModule s M)
            (moduleShiftInElement R D s M) (moduleShiftOutElement R D s M)
            (add_neg_cancel s)) (zero_add k) :=
        (compose_assoc_of_sum (A := R) (D := RightModule R D)
          (w := shiftModule s M) (x := M) (y := shiftModule s M) (z := N)
          (moduleShiftOutElement R D s M) (moduleShiftInElement R D s M) f
          (add_neg_cancel s) ht (zero_add k)).symm
      _ = f := by rw [moduleShiftOutIn R D s M, compose_unit]

  rw [hf, zero_compose] at he
  exact he.symm

variable {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarHom_eq_zero_of_shiftedInclusions (N : ModuleCategory R D) (k : ℤ)
    (f : (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) N)).X k)
    (hf : ∀ s : dgCoherentBarIndex I,
      compose R (x := dgCoherentBarSource R D F s)
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) N)
        f (dgCoherentBarShiftedInclusion R D F s) rfl = 0) : f = 0 := by
  apply (dgCoherentBarHomEquiv R D F N k).injective
  funext s
  rw [dgCoherentBarHomEquiv_apply, dgCoherentBarHomEquiv_apply]
  simp only [map_zero]
  apply dgModuleHom_eq_zero_of_comp_shiftIn R D (s.1 : ℤ) _ rfl
  have hs := hf s
  unfold dgCoherentBarShiftedInclusion at hs
  rw [compose_units_smul_right, moduleHomClosedInsertion R D
    (S := ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s))
    (M := dgCoherentBarFamily R D F s) (N := dgCoherentBarGraded R D F) (P := N)] at hs
  have hz := congrArg (fun z => (s.1 : ℤ).negOnePow • z) hs
  simpa only [smul_smul, Int.units_mul_self, one_smul, smul_zero] using hz

end SerrePositivity.InfinityCategories
