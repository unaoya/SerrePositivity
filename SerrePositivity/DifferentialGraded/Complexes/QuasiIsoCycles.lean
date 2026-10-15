module
public import SerrePositivity.DifferentialGraded.Complexes.ConeElements
public import SerrePositivity.DifferentialGraded.Complexes.AcyclicCone
public import SerrePositivity.DifferentialGraded.Complexes.TowerPrimitives

/-! # quasiIsoによるcycleの持ち上げと境界の反映

coneのacyclic性を用い、原像と境界の証人を具体的な要素として取り出す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {K L : Complex A}

lemma complexCone_d_fst (f : K ⟶ L) (q : ℤ) (z : (mappingCone f).X q) :
    (mappingCone.fst f).val.v (q + 1) (q + 1 + 1) rfl
      ((mappingCone f).d q (q + 1) z) =
        -K.d (q + 1) (q + 1 + 1) ((mappingCone.fst f).val.v q (q + 1) rfl z) :=
  congrArg (fun a => a z) (mappingCone.d_fst_v f q (q + 1) (q + 1 + 1) rfl rfl)

lemma complexCone_d_snd (f : K ⟶ L) (q : ℤ) (z : (mappingCone f).X q) :
    (mappingCone.snd f).v (q + 1) (q + 1) (add_zero _)
      ((mappingCone f).d q (q + 1) z) =
        f.f (q + 1) ((mappingCone.fst f).val.v q (q + 1) rfl z) +
          L.d q (q + 1) ((mappingCone.snd f).v q q (add_zero q) z) :=
  congrArg (fun a => a z) (mappingCone.d_snd_v f q (q + 1) rfl)

lemma complexAcyclic_boundary_succ {C : Complex A} (hC : C.Acyclic) (q : ℤ)
    (z : C.X (q + 1)) (hz : C.d (q + 1) (q + 1 + 1) z = 0) :
    ∃ t : C.X q, C.d q (q + 1) t = z := by
  have h := complexAcyclic_boundary (K := C) hC (q + 1) z hz
  rw [show q + 1 - 1 = q by omega] at h
  exact h

lemma complexQuasiIso_cycle_lift (f : K ⟶ L) (hf : QuasiIso f) (q : ℤ)
    (z : L.X (q + 1)) (hz : L.d (q + 1) (q + 1 + 1) z = 0) :
    ∃ a : K.X (q + 1), K.d (q + 1) (q + 1 + 1) a = 0 ∧
      ∃ b : L.X q, L.d q (q + 1) b = z - f.f (q + 1) a := by
  have hC := (complex_quasiIso_iff_acyclic_cone A f).1 hf
  have hinr : (mappingCone f).d (q + 1) (q + 1 + 1)
      ((mappingCone.inr f).f (q + 1) z) = 0 := by
    have h := congrArg (fun a => a z) ((mappingCone.inr f).comm (q + 1) (q + 1 + 1))
    change (mappingCone f).d (q + 1) (q + 1 + 1) ((mappingCone.inr f).f (q + 1) z) =
      (mappingCone.inr f).f (q + 1 + 1) (L.d (q + 1) (q + 1 + 1) z) at h
    exact h.trans (by rw [hz, map_zero])
  obtain ⟨t, ht⟩ := complexAcyclic_boundary_succ A hC q _ hinr
  let a := (mappingCone.fst f).val.v q (q + 1) rfl t
  let b := (mappingCone.snd f).v q q (add_zero q) t
  have hfst := complexCone_d_fst A f q t
  rw [ht, ← ModuleCat.comp_apply, mappingCone.inr_f_fst_v] at hfst
  have ha : K.d (q + 1) (q + 1 + 1) a = 0 := by
    change (0 : K.X (q + 1 + 1)) = -K.d (q + 1) (q + 1 + 1) a at hfst
    exact neg_eq_zero.mp hfst.symm
  have hsnd := complexCone_d_snd A f q t
  rw [ht, ← ModuleCat.comp_apply, mappingCone.inr_f_snd_v, ModuleCat.id_apply] at hsnd
  refine ⟨a, ha, b, ?_⟩
  change z = f.f (q + 1) a + L.d q (q + 1) b at hsnd
  exact eq_sub_of_add_eq ((add_comm _ _).trans hsnd.symm)

lemma complexQuasiIso_boundary_reflect (f : K ⟶ L) (hf : QuasiIso f) (q : ℤ)
    (a : K.X (q + 1)) (ha : K.d (q + 1) (q + 1 + 1) a = 0)
    (b : L.X q) (hb : L.d q (q + 1) b = f.f (q + 1) a) :
    ∃ t : K.X q, K.d q (q + 1) t = a := by
  let z := complexConeElementMk A f q a (-b)
  have hz : (mappingCone f).d q (q + 1) z = 0 := by
    apply complexConeElement_ext A f (q + 1)
    · rw [complexCone_d_fst, complexConeElementMk_fst, ha, neg_zero, map_zero]
    · rw [complexCone_d_snd, complexConeElementMk_fst, complexConeElementMk_snd,
        map_neg, hb, add_neg_cancel, map_zero]
  obtain ⟨s, hs⟩ := complexAcyclic_boundary
    (K := mappingCone f) ((complex_quasiIso_iff_acyclic_cone A f).1 hf) q z hz
  let t := -(mappingCone.fst f).val.v (q - 1) q (by omega) s
  refine ⟨t, ?_⟩
  have h := congrArg (fun a => a s) (mappingCone.d_fst_v' f q (q + 1) rfl)
  change (mappingCone.fst f).val.v q (q + 1) rfl ((mappingCone f).d (q - 1) q s) =
    -K.d q (q + 1) ((mappingCone.fst f).val.v (q - 1) q (by omega) s) at h
  rw [hs, complexConeElementMk_fst] at h
  exact (map_neg _ _).trans h.symm

end SerrePositivity.DifferentialGraded
