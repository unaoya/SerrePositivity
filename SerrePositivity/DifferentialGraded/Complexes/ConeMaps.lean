module
public import SerrePositivity.DifferentialGraded.Complexes.ConeHom
public import SerrePositivity.HomologicalAlgebra.Complex.Cone

/-! # cone の connecting map の全次数自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {K P Q R S : Complex A}

/-- cone の第一射影後の作用の斉次成分。 -/
lemma coneMapCochain_fst_v (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p)
    (i j : ℤ) (hij : i + p = j) :
    (coneMapCochain f g a b).v i j hij ≫ (mappingCone.fst g).val.v j (j + 1) rfl =
      p.negOnePow • ((mappingCone.fst f).val.v i (i + 1) rfl ≫
        a.v (i + 1) (j + 1) (by omega)) := by
  have h := Cochain.congr_v (coneMapCochain_fst f g a b) i (j + 1) (by omega)
  simpa only [Cochain.units_smul_v,
    Cochain.comp_v _ _ (by omega : p + 1 = p + 1) i j (j + 1) hij rfl,
    Cochain.comp_v _ _ (by omega : 1 + p = p + 1) i (i + 1) (j + 1) rfl (by omega)] using h

/-- 既存 cone triangle の connecting map は全次数 Hom に対して自然。 -/
lemma coneHomMap_connecting (f : P ⟶ Q) (g : R ⟶ S)
    (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S) (h) :
    coneHomMap f g a b h ≫ homPostcompose (mappingCone f) (mappingCone.triangle g).mor₃ =
      a ≫ shiftHom 1 P R ≫ homPrecompose (mappingCone.triangle f).mor₃ (R⟦(1 : ℤ)⟧) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  apply Cochain.ext
  intro i j hij
  change ((coneMapCochain f g (a.f p t) (b.f p t)).comp
    (Cochain.ofHom (mappingCone.triangle g).mor₃) (add_zero p)).v i j hij =
    ((Cochain.ofHom (mappingCone.triangle f).mor₃).comp
      ((shiftHom 1 P R).f p (a.f p t)) (zero_add p)).v i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v, shiftHom_v,
    SerrePositivity.coneTriangle_mor₃_f, SerrePositivity.coneTriangle_mor₃_f]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id, one_mul, Preadditive.comp_neg]
  rw [coneMapCochain_fst_v]
  simp only [Preadditive.neg_comp, Linear.comp_units_smul, smul_neg]

/-- 閉次数0の cone 対角作用は Mathlib の可換 square の cone 射と一致。 -/
lemma coneMapCochain_ofHom (f : P ⟶ Q) (g : R ⟶ S)
    (a : P ⟶ R) (b : Q ⟶ S) (h : f ≫ b = a ≫ g) :
    Cochain.ofHom (mappingCone.map f g a b h) =
      coneMapCochain f g (Cochain.ofHom a) (Cochain.ofHom b) := by
  apply Cochain.ext₀
  intro i
  rw [Cochain.ofHom_v, coneMapCochain_v]
  apply mappingCone.ext_from f (i + 1) i rfl
  · simp only [mappingCone.map, mappingCone.inl_v_desc_f,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Int.negOnePow_zero, one_smul,
      Preadditive.comp_add, mappingCone.inl_v_fst_v_assoc,
      mappingCone.inl_v_snd_v_assoc, zero_comp, add_zero]
  · simp only [mappingCone.map, mappingCone.inr_f_desc_f, HomologicalComplex.comp_f,
      Cochain.ofHom_v, Int.negOnePow_zero, one_smul, Preadditive.comp_add,
      mappingCone.inr_f_fst_v_assoc, mappingCone.inr_f_snd_v_assoc,
      zero_comp, zero_add]
end SerrePositivity.DifferentialGraded
