module

public import SerrePositivity.HomologicalAlgebra.KoszulAlgebraTorComparison

/-! # Standard Tor coefficient actions and actual algebra-valued Tor modules

Use the original ordinaryTorIso and arbitrary projective resolutions. No new
module structure on ordinary Tor is postulated.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]

/-- The original ordinary Tor comparison, in the direction of algebra homology. -/
def algebraResolutionTorComparison {M : ModuleCat.{u} R}
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsResolutionOf K M) (i : ℕ) :
    ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).obj M ≅
      (ModuleCat.restrictScalars (algebraMap R C)).obj
        ((baseChange (algebraMap R C) K).homology (-(i : ℤ))) :=
  (ordinaryTorIso (R := R) (T := C) M K hK i).symm.toModuleIso

/-- Every coefficient scalar agrees with the actual C-module scalar action. -/
@[reassoc] lemma algebraResolutionTorComparison_coefficient_scalar
    {M : ModuleCat.{u} R} {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsResolutionOf K M) (i : ℕ) (c : C) :
    torCoefficientScalarEndomorphism C M i c ≫
        (algebraResolutionTorComparison (C := C) hK i).hom =
      (algebraResolutionTorComparison (C := C) hK i).hom ≫
        (ModuleCat.restrictScalars (algebraMap R C)).map
          (c • 𝟙 ((baseChange (algebraMap R C) K).homology (-(i : ℤ)))) := by
  let U := ModuleCat.restrictScalars (algebraMap R C)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) (-(i : ℤ))
  let eT := torModuleIsoCochain C hK i
  let eK := algebraBaseChangeTensorIso (C := C) K
  let q := (restrictCochainHomologyIso (R := R) (C := C) (-(i : ℤ))).app
    (baseChange (algebraMap R C) K)
  let α := (NatTrans.mapHomologicalComplex
    ((tensoringLeft (ModuleCat R)).map (ModuleCat.ofHom (LinearMap.mulLeft R c))) (.up ℤ)).app K
  have ht : torCoefficientScalarEndomorphism C M i c ≫ eT.hom = eT.hom ≫ H.map α :=
    leftDerivedIsoCochain_natTrans _ _
      ((tensoringLeft (ModuleCat R)).map (ModuleCat.ofHom (LinearMap.mulLeft R c))) hK i
  have hk : α ≫ eK.inv = eK.inv ≫ (U.mapHomologicalComplex (.up ℤ)).map
      (c • 𝟙 (baseChange (algebraMap R C) K)) := by
    have h := algebraBaseChangeTensorIso_coefficient_scalar K c
    calc
      α ≫ eK.inv = eK.inv ≫ (eK.hom ≫ α) ≫ eK.inv := by simp
      _ = eK.inv ≫ ((U.mapHomologicalComplex (.up ℤ)).map
          (c • 𝟙 _) ≫ eK.hom) ≫ eK.inv := by rw [← h]
      _ = _ := by simp [Category.assoc]
  have hkH := congrArg H.map hk
  simp only [Functor.map_comp] at hkH
  have hq : H.map ((U.mapHomologicalComplex (.up ℤ)).map
      (c • 𝟙 (baseChange (algebraMap R C) K))) ≫ q.hom =
      q.hom ≫ U.map (c • 𝟙 ((baseChange (algebraMap R C) K).homology (-(i : ℤ)))) := by
    have h := (restrictCochainHomologyIso (R := R) (C := C) (-(i : ℤ))).hom.naturality
      (c • 𝟙 (baseChange (algebraMap R C) K))
    change H.map _ ≫ q.hom = q.hom ≫
      U.map (HomologicalComplex.homologyMap (c • 𝟙 _) (-(i : ℤ))) at h
    simpa only [homologyMap_smul, HomologicalComplex.homologyMap_id] using h
  change _ ≫ (eT.hom ≫ H.map eK.inv ≫ q.hom) =
    (eT.hom ≫ H.map eK.inv ≫ q.hom) ≫ _
  rw [reassoc_of% ht, reassoc_of% hkH, hq]
  simp only [Category.assoc]
  rfl

/-- Standard Tor and the actual algebra-valued Tor, using the same chosen resolution. -/
def torAlgebraComparison (M : ModuleCat.{u} R) (i : ℕ) :
    ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).obj M ≅
      (ModuleCat.restrictScalars (algebraMap R C)).obj
        (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M) :=
  algebraResolutionTorComparison (isResolutionOf_extRes (projectiveResolution M)) i ≪≫
    (ModuleCat.restrictScalars (algebraMap R C)).mapIso
      (torIsoCochain (algebraMap R C)
        (isResolutionOf_extRes (projectiveResolution M)) i).symm

@[reassoc] lemma torAlgebraComparison_coefficient_scalar
    (M : ModuleCat.{u} R) (i : ℕ) (c : C) :
    torCoefficientScalarEndomorphism C M i c ≫ (torAlgebraComparison (C := C) M i).hom =
      (torAlgebraComparison (C := C) M i).hom ≫
        (ModuleCat.restrictScalars (algebraMap R C)).map
          (c • 𝟙 (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M)) := by
  let U := ModuleCat.restrictScalars (algebraMap R C)
  let e := torIsoCochain (algebraMap R C)
    (isResolutionOf_extRes (projectiveResolution M)) i
  have hc : (c • 𝟙 _) ≫ e.inv = e.inv ≫ (c • 𝟙 _) := by simp
  have hu := congrArg U.map hc
  simp only [Functor.map_comp] at hu
  simp only [torAlgebraComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, algebraResolutionTorComparison_coefficient_scalar, Category.assoc, hu]
  simp only [Category.assoc]
  rfl

/-- Zero action is equivalent under the original comparison, for every coefficient element. -/
lemma torAlgebraComparison_scalar_eq_zero_iff (M : ModuleCat.{u} R) (i : ℕ) (c : C) :
    torCoefficientScalarEndomorphism C M i c = 0 ↔
      c • 𝟙 (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M) = 0 := by
  let U := ModuleCat.restrictScalars (algebraMap R C)
  let e := torAlgebraComparison (C := C) M i
  have h := torAlgebraComparison_coefficient_scalar M i c
  constructor
  · intro hc
    have hu : U.map (c • 𝟙 (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M)) = 0 := by
      rw [← cancel_epi e.hom, comp_zero, ← h, hc, zero_comp]
    apply U.map_injective
    simpa only [Functor.map_zero] using hu
  · intro hc
    rw [← cancel_mono e.hom, zero_comp, h, hc, Functor.map_zero, comp_zero]

/-- Standard zero action is exactly annihilation in the actual algebra-valued Tor module. -/
lemma torAlgebraComparison_scalar_zero_iff_forall (M : ModuleCat.{u} R) (i : ℕ) (c : C) :
    torCoefficientScalarEndomorphism C M i c = 0 ↔
      ∀ x : ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M, c • x = 0 := by
  rw [torAlgebraComparison_scalar_eq_zero_iff]
  constructor
  · intro h x
    exact congrArg (fun f => f.hom x) h
  · intro h
    ext x
    exact h x

/-- The original ideal action becomes the ordinary annihilator condition over any
coefficient source B, under the actual restriction along ψ. -/
lemma torAlgebraComparison_restricted_annihilator_iff
    (B : Type u) [CommRing B] (ψ : B →+* C) (I : Ideal B)
    (M : ModuleCat.{u} R) (i : ℕ) :
    (∀ b ∈ I, torCoefficientScalarEndomorphism C M i (ψ b) = 0) ↔
      (letI := Module.compHom
        (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M) ψ
       I ≤ Module.annihilator B
         (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M)) := by
  letI := Module.compHom
    (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M) ψ
  constructor
  · intro h b hb
    rw [Module.mem_annihilator]
    exact (torAlgebraComparison_scalar_zero_iff_forall M i (ψ b)).mp (h b hb)
  · intro h b hb
    apply (torAlgebraComparison_scalar_zero_iff_forall M i (ψ b)).mpr
    exact Module.mem_annihilator.mp (h hb)

end SerrePositivity
