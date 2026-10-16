module
public import SerrePositivity.DifferentialGraded.Complexes.ConeElements

/-! # 四つの包含・射影からの標準cone比較の可逆性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {X Y K : Complex A}
variable (f : X ⟶ Y) (α : Cochain X K (-1)) (β : Y ⟶ K)
  (γ : Cochain K X 1) (η : Cochain K Y 0)
  (hδ : δ (-1) 0 α = Cochain.ofHom (f ≫ β))

def complexConeDescInverseElement (n : ℤ) (z : K.X n) : (mappingCone f).X n :=
  complexConeElementMk A f n (γ.v n (n + 1) rfl z) (η.v n n (add_zero n) z)

lemma complexConeDesc_fst
    (hαγ : α.comp γ (neg_add_cancel 1) = Cochain.ofHom (𝟙 X))
    (hβγ : (Cochain.ofHom β).comp γ (zero_add 1) = 0) (n : ℤ) :
    (mappingCone.desc f α β hδ).f n ≫ γ.v n (n + 1) rfl =
      (mappingCone.fst f).val.v n (n + 1) rfl := by
  apply mappingCone.ext_from f (n + 1) n rfl
  · rw [← Category.assoc, mappingCone.inl_v_desc_f, mappingCone.inl_v_fst_v]
    have h := Cochain.congr_v hαγ (n + 1) (n + 1) (add_zero (n + 1))
    rw [Cochain.comp_v _ _ _ (n + 1) n (n + 1) (by omega) rfl,
      Cochain.ofHom_v, HomologicalComplex.id_f] at h
    exact h
  · rw [← Category.assoc, mappingCone.inr_f_desc_f, mappingCone.inr_f_fst_v]
    have h := Cochain.congr_v hβγ n (n + 1) rfl
    simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] using h

lemma complexConeDesc_snd
    (hαη : α.comp η (add_zero (-1)) = 0)
    (hβη : (Cochain.ofHom β).comp η (zero_add 0) = Cochain.ofHom (𝟙 Y)) (n : ℤ) :
    (mappingCone.desc f α β hδ).f n ≫ η.v n n (add_zero n) =
      (mappingCone.snd f).v n n (add_zero n) := by
  apply mappingCone.ext_from f (n + 1) n rfl
  · rw [← Category.assoc, mappingCone.inl_v_desc_f, mappingCone.inl_v_snd_v]
    have h := Cochain.congr_v hαη (n + 1) n (by omega)
    simpa only [Cochain.comp_zero_cochain_v, Cochain.zero_v] using h
  · rw [← Category.assoc, mappingCone.inr_f_desc_f, mappingCone.inr_f_snd_v]
    have h := Cochain.congr_v hβη n n (add_zero n)
    simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, HomologicalComplex.id_f] using h

lemma complexConeDesc_rightInverse
    (hd : γ.comp α (add_neg_cancel 1) + η.comp (Cochain.ofHom β) (add_zero 0) =
      Cochain.ofHom (𝟙 K)) (n : ℤ) :
    Function.RightInverse (complexConeDescInverseElement A f γ η n)
      ((mappingCone.desc f α β hδ).f n) := by
  intro z
  have h := Cochain.congr_v hd n n (add_zero n)
  rw [Cochain.add_v, Cochain.comp_v _ _ _ n (n + 1) n rfl (by omega),
    Cochain.comp_zero_cochain_v] at h
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f] at h
  have hz := congrArg (fun p => p z) h
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply, ModuleCat.id_apply] at hz
  rw [complexConeDescInverseElement, complexConeElementMk, map_add]
  change ((mappingCone.inl f).v (n + 1) n (by omega) ≫ (mappingCone.desc f α β hδ).f n)
      (γ.v n (n + 1) rfl z) +
    ((mappingCone.inr f).f n ≫ (mappingCone.desc f α β hδ).f n) (η.v n n (add_zero n) z) = z
  rw [mappingCone.inl_v_desc_f, mappingCone.inr_f_desc_f]
  exact hz

lemma complexConeDesc_leftInverse
    (hαγ : α.comp γ (neg_add_cancel 1) = Cochain.ofHom (𝟙 X))
    (hαη : α.comp η (add_zero (-1)) = 0)
    (hβγ : (Cochain.ofHom β).comp γ (zero_add 1) = 0)
    (hβη : (Cochain.ofHom β).comp η (zero_add 0) = Cochain.ofHom (𝟙 Y)) (n : ℤ) :
    Function.LeftInverse (complexConeDescInverseElement A f γ η n)
      ((mappingCone.desc f α β hδ).f n) := by
  intro z
  apply complexConeElement_ext A f n
  · rw [complexConeDescInverseElement, complexConeElementMk_fst,
      ← ModuleCat.comp_apply, complexConeDesc_fst A f α β γ hδ hαγ hβγ n]
  · rw [complexConeDescInverseElement, complexConeElementMk_snd,
      ← ModuleCat.comp_apply, complexConeDesc_snd A f α β η hδ hαη hβη n]

lemma complexConeDesc_bijective
    (hαγ : α.comp γ (neg_add_cancel 1) = Cochain.ofHom (𝟙 X))
    (hαη : α.comp η (add_zero (-1)) = 0)
    (hβγ : (Cochain.ofHom β).comp γ (zero_add 1) = 0)
    (hβη : (Cochain.ofHom β).comp η (zero_add 0) = Cochain.ofHom (𝟙 Y))
    (hd : γ.comp α (add_neg_cancel 1) + η.comp (Cochain.ofHom β) (add_zero 0) =
      Cochain.ofHom (𝟙 K)) (n : ℤ) : Function.Bijective ((mappingCone.desc f α β hδ).f n) :=
  ⟨(complexConeDesc_leftInverse A f α β γ η hδ hαγ hαη hβγ hβη n).injective,
    (complexConeDesc_rightInverse A f α β γ η hδ hd n).surjective⟩

lemma complexConeDesc_isIso
    (hαγ : α.comp γ (neg_add_cancel 1) = Cochain.ofHom (𝟙 X))
    (hαη : α.comp η (add_zero (-1)) = 0)
    (hβγ : (Cochain.ofHom β).comp γ (zero_add 1) = 0)
    (hβη : (Cochain.ofHom β).comp η (zero_add 0) = Cochain.ofHom (𝟙 Y))
    (hd : γ.comp α (add_neg_cancel 1) + η.comp (Cochain.ofHom β) (add_zero 0) =
      Cochain.ofHom (𝟙 K)) : IsIso (mappingCone.desc f α β hδ) := by
  let (n : ℤ) : IsIso ((mappingCone.desc f α β hδ).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (complexConeDesc_bijective A f α β γ η hδ hαγ hαη hβγ hβη hd n)
  exact HomologicalComplex.Hom.isIso_of_components _

end SerrePositivity.DifferentialGraded
