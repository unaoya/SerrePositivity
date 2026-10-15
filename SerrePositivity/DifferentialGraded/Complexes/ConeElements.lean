module
public import SerrePositivity.DifferentialGraded.Complexes.ConeDesc

/-! # module複体のconeの各次数の要素と二つの射影 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {M N : Complex A}

def complexConeElementMk (f : M ⟶ N) (q : ℤ) (a : M.X (q + 1)) (b : N.X q) :
    (mappingCone f).X q :=
  (mappingCone.inl f).v (q + 1) q (by omega) a + (mappingCone.inr f).f q b

lemma complexConeElementMk_fst (f : M ⟶ N) (q : ℤ) (a : M.X (q + 1)) (b : N.X q) :
    (mappingCone.fst f).val.v q (q + 1) rfl (complexConeElementMk A f q a b) = a := by
  rw [complexConeElementMk, map_add, ← ModuleCat.comp_apply, mappingCone.inl_v_fst_v,
    ModuleCat.id_apply, ← ModuleCat.comp_apply, mappingCone.inr_f_fst_v]
  simp

lemma complexConeElementMk_snd (f : M ⟶ N) (q : ℤ) (a : M.X (q + 1)) (b : N.X q) :
    (mappingCone.snd f).v q q (add_zero q) (complexConeElementMk A f q a b) = b := by
  rw [complexConeElementMk, map_add, ← ModuleCat.comp_apply, mappingCone.inl_v_snd_v,
    ← ModuleCat.comp_apply, mappingCone.inr_f_snd_v, ModuleCat.id_apply]
  simp

lemma complexConeElement_ext (f : M ⟶ N) (q : ℤ) {z w : (mappingCone f).X q}
    (hfst : (mappingCone.fst f).val.v q (q + 1) rfl z =
      (mappingCone.fst f).val.v q (q + 1) rfl w)
    (hsnd : (mappingCone.snd f).v q q (add_zero q) z =
      (mappingCone.snd f).v q q (add_zero q) w) : z = w := by
  have hm : moduleElementMap A _ z = moduleElementMap A _ w := by
    apply mappingCone.ext_to f q (q + 1) rfl
    · apply (moduleElementEquiv A _).injective
      change (mappingCone.fst f).val.v q (q + 1) rfl ((1 : A) • z) =
        (mappingCone.fst f).val.v q (q + 1) rfl ((1 : A) • w)
      simpa only [one_smul] using hfst
    · apply (moduleElementEquiv A _).injective
      change (mappingCone.snd f).v q q (add_zero q) ((1 : A) • z) =
        (mappingCone.snd f).v q q (add_zero q) ((1 : A) • w)
      simpa only [one_smul] using hsnd
  have he := congrArg (fun a => a (1 : A)) hm
  change (1 : A) • z = (1 : A) • w at he
  simpa only [one_smul] using he

lemma complexConeElementMk_eta (f : M ⟶ N) (q : ℤ) (z : (mappingCone f).X q) :
    complexConeElementMk A f q ((mappingCone.fst f).val.v q (q + 1) rfl z)
      ((mappingCone.snd f).v q q (add_zero q) z) = z := by
  apply complexConeElement_ext A f q
  · exact complexConeElementMk_fst A f q _ _
  · exact complexConeElementMk_snd A f q _ _

end SerrePositivity.DifferentialGraded
