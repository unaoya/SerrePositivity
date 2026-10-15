module
public import SerrePositivity.DifferentialGraded.Complexes.ConeMaps

/-! # 明示的なshift射を用いる既存cone shift同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {K L : Complex A}

def complexConeShiftIso (f : K ⟶ L) (s : ℤ) (ψ : K⟦s⟧ ⟶ L⟦s⟧) (hψ : ψ = f⟦s⟧') :
    (mappingCone f)⟦s⟧ ≅ mappingCone ψ := by
  subst ψ
  exact mappingCone.shiftIso f s

lemma complexConeShiftIso_hom_cochain (f : K ⟶ L) (s : ℤ) (ψ : K⟦s⟧ ⟶ L⟦s⟧)
    (hψ : ψ = f⟦s⟧') :
    Cochain.ofHom (complexConeShiftIso f s ψ hψ).hom =
      mappingCone.liftCochain ψ (s.negOnePow • (mappingCone.fst f).val.shift s)
        ((mappingCone.snd f).shift s) (zero_add 1) := by
  subst ψ
  simp only [complexConeShiftIso, mappingCone.shiftIso, mappingCone.ofHom_lift,
    Cocycle.coe_units_smul, Cocycle.shift_coe]

lemma complexConeShiftIso_inv_cochain (f : K ⟶ L) (s : ℤ) (ψ : K⟦s⟧ ⟶ L⟦s⟧)
    (hψ : ψ = f⟦s⟧') :
    Cochain.ofHom (complexConeShiftIso f s ψ hψ).inv =
      mappingCone.descCochain ψ (s.negOnePow • (mappingCone.inl f).shift s)
        (Cochain.ofHom ((mappingCone.inr f)⟦s⟧')) (neg_add_cancel 1) := by
  subst ψ
  simp only [complexConeShiftIso, mappingCone.shiftIso, mappingCone.ofHom_desc]

lemma complexConeShift_lift_condition (f : K ⟶ L) (s : ℤ) (ψ : K⟦s⟧ ⟶ L⟦s⟧)
    (hψ : ψ = f⟦s⟧') :
    δ 0 1 ((mappingCone.snd f).shift s) +
      (s.negOnePow • (mappingCone.fst f).val.shift s).comp (Cochain.ofHom ψ) (add_zero 1) = 0 := by
  subst ψ
  ext p q hpq
  dsimp
  simp only [Cochain.δ_shift, mappingCone.δ_snd, Cochain.shift_neg, smul_neg, Cochain.neg_v,
    shiftFunctor_obj_X', Cochain.units_smul_v, Cochain.shift_v', Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, Cochain.units_smul_comp, shiftFunctor_map_f']
  simp

lemma complexConeShift_desc_condition (f : K ⟶ L) (s : ℤ) (ψ : K⟦s⟧ ⟶ L⟦s⟧)
    (hψ : ψ = f⟦s⟧') :
    δ (-1) 0 (s.negOnePow • (mappingCone.inl f).shift s) =
      Cochain.ofHom (ψ ≫ (mappingCone.inr f)⟦s⟧') := by
  subst ψ
  ext p
  dsimp
  simp only [Int.reduceNeg, δ_units_smul, Cochain.δ_shift, mappingCone.δ_inl,
    Cochain.ofHom_comp, smul_smul, Int.units_mul_self, one_smul, Cochain.shift_v',
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v, shiftFunctor_obj_X', shiftFunctor_map_f']


lemma complexConeShift_inr (f : K ⟶ L) (s : ℤ) (ψ : K⟦s⟧ ⟶ L⟦s⟧)
    (hψ : ψ = f⟦s⟧') :
    (s.negOnePow • (mappingCone.inr f)⟦s⟧') ≫ (complexConeShiftIso f s ψ hψ).hom =
      (s.negOnePow • 𝟙 (L⟦s⟧)) ≫ mappingCone.inr ψ := by
  subst ψ
  exact (mappingCone.shiftTriangleIso f s).hom.comm₂

lemma complexConeShift_connecting (f : K ⟶ L) (s : ℤ) (ψ : K⟦s⟧ ⟶ L⟦s⟧)
    (hψ : ψ = f⟦s⟧') :
    (s.negOnePow • (mappingCone.triangle f).mor₃⟦s⟧') ≫
      (shiftFunctorComm (Complex A) 1 s).hom.app K =
        (complexConeShiftIso f s ψ hψ).hom ≫ (mappingCone.triangle ψ).mor₃ := by
  subst ψ
  let γ : (mappingCone f)⟦s⟧ ⟶ (K⟦(1 : ℤ)⟧)⟦s⟧ := (mappingCone.triangle f).mor₃⟦s⟧'
  let c : (K⟦(1 : ℤ)⟧)⟦s⟧ ⟶ (K⟦s⟧)⟦(1 : ℤ)⟧ :=
    (shiftFunctorComm (Complex A) 1 s).hom.app K
  let γ' : mappingCone (f⟦s⟧') ⟶ (K⟦s⟧)⟦(1 : ℤ)⟧ := (mappingCone.triangle (f⟦s⟧')).mor₃
  have h := (mappingCone.shiftTriangleIso f s).hom.comm₃
  dsimp only [mappingCone.shiftTriangleIso, Pretriangulated.Triangle.isoMk,
    Pretriangulated.Triangle.homMk, Pretriangulated.Triangle.shiftFunctor] at h
  change (s.negOnePow • (γ ≫ c)) ≫ (𝟙 (K⟦s⟧))⟦(1 : ℤ)⟧' =
    (mappingCone.shiftIso f s).hom ≫ γ' at h
  rw [(CategoryTheory.shiftFunctor (Complex A) (1 : ℤ)).map_id (K⟦s⟧), Category.comp_id] at h
  exact (Linear.units_smul_comp s.negOnePow γ c).trans h

end SerrePositivity.DifferentialGraded
