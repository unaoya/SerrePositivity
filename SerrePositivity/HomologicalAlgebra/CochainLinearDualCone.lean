module
public import SerrePositivity.HomologicalAlgebra.MappingConeLinearDual
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # A shifted dual of a mapping cone is the cone of the reversed dual map -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex.homotopyCofiber
variable {R : Type u} [CommRing R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)

/-- Product coordinates of an ordinary cone term. -/
def mappingConeTermProdIso (q : ℤ) :
    (CochainComplex.mappingCone φ).X q ≅ ModuleCat.of R (K.X (q + 1) × L.X q) :=
  XIsoBiprod φ q (q + 1) rfl ≪≫ ModuleCat.biprodIsoProd _ _

/-- The first product projection is the actual cone projection. -/
lemma mappingConeTermProdIso_fst (q : ℤ) :
    (mappingConeTermProdIso φ q).hom ≫
        ModuleCat.ofHom (LinearMap.fst R (K.X (q + 1)) (L.X q)) =
      fstX φ q (q + 1) rfl := by
  have hb : (ModuleCat.biprodIsoProd (K.X (q + 1)) (L.X q)).hom ≫
      ModuleCat.ofHom (LinearMap.fst R (K.X (q + 1)) (L.X q)) = biprod.fst := by
    apply (cancel_epi (ModuleCat.biprodIsoProd (K.X (q + 1)) (L.X q)).inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      ModuleCat.biprodIsoProd_inv_comp_fst]
  dsimp only [mappingConeTermProdIso, Iso.trans_hom]
  rw [Category.assoc, hb]
  rfl

/-- The second product projection is the actual cone projection. -/
lemma mappingConeTermProdIso_snd (q : ℤ) :
    (mappingConeTermProdIso φ q).hom ≫
        ModuleCat.ofHom (LinearMap.snd R (K.X (q + 1)) (L.X q)) = sndX φ q := by
  have hb : (ModuleCat.biprodIsoProd (K.X (q + 1)) (L.X q)).hom ≫
      ModuleCat.ofHom (LinearMap.snd R (K.X (q + 1)) (L.X q)) = biprod.snd := by
    apply (cancel_epi (ModuleCat.biprodIsoProd (K.X (q + 1)) (L.X q)).inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      ModuleCat.biprodIsoProd_inv_comp_snd]
  dsimp only [mappingConeTermProdIso, Iso.trans_hom]
  rw [Category.assoc, hb]
  apply ext_from_X φ (q + 1) q rfl
  · simp only [← Category.assoc, inlX_XIsoBiprod_hom, biprod.inl_snd, inlX_sndX]
  · simp only [← Category.assoc, inrX_XIsoBiprod_hom, biprod.inr_snd, inrX_sndX]

/-- First component of the actual cone differential. -/
lemma mappingConeTermProdIso_d_fst (q : ℤ) (x : (CochainComplex.mappingCone φ).X q) :
    ((mappingConeTermProdIso φ (q + 1)).hom
      ((CochainComplex.mappingCone φ).d q (q + 1) x)).1 =
      -(K.d (q + 1) (q + 1 + 1) ((mappingConeTermProdIso φ q).hom x).1) := by
  have h := d_fstX φ q (q + 1) (q + 1 + 1) rfl rfl
  rw [← mappingConeTermProdIso_fst φ (q + 1), ← mappingConeTermProdIso_fst φ q] at h
  exact congrArg (fun f => f.hom x) h

/-- Second component of the actual cone differential, including its cross term. -/
lemma mappingConeTermProdIso_d_snd (q : ℤ) (x : (CochainComplex.mappingCone φ).X q) :
    ((mappingConeTermProdIso φ (q + 1)).hom
      ((CochainComplex.mappingCone φ).d q (q + 1) x)).2 =
      φ.f (q + 1) ((mappingConeTermProdIso φ q).hom x).1 +
        L.d q (q + 1) ((mappingConeTermProdIso φ q).hom x).2 := by
  have h := d_sndX φ q (q + 1) rfl
  rw [← mappingConeTermProdIso_snd φ (q + 1), ← mappingConeTermProdIso_fst φ q,
    ← mappingConeTermProdIso_snd φ q] at h
  exact congrArg (fun f => f.hom x) h

/-- Changing the label of the shifted source summand only transports its source object. -/
lemma mappingCone_inlX_cast (q r : ℤ) (h : q + 1 = r) :
    (K.XIsoOfEq h).inv ≫ inlX φ (q + 1) q rfl = inlX φ r q h := by
  subst r
  simp

/-- Swapping the dual summands and negating the old source gives the shifted cone comparison. -/
def cochainLinearDualConeShiftTermIso (M : ModuleCat.{u} R) (i : ℤ) :
    (((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M)⟦(1 : ℤ)⟧).X i ≅
      (CochainComplex.mappingCone ((cochainLinearDualMap φ).app M)).X i := by
  let E := mappingConeTargetHomEquiv φ M (0 - (i + 1))
  let e : (K.X (0 - (i + 1) + 1) ⟶ M) ≃ₗ[R] (K.X (0 - i) ⟶ M) :=
    Linear.homCongr R (K.XIsoOfEq (by omega)) (Iso.refl M)
  exact (E.trans ((LinearEquiv.prodComm R _ _).trans
    ((LinearEquiv.refl R _).prodCongr (e.trans (LinearEquiv.neg R))))).toModuleIso ≪≫
      (mappingConeTermProdIso ((cochainLinearDualMap φ).app M) i).symm

/-- The first comparison coordinate is the old target restriction. -/
lemma cochainLinearDualConeShiftTermIso_fst (M : ModuleCat.{u} R) (i : ℤ)
    (f : (((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M)⟦(1 : ℤ)⟧).X i) :
    ((mappingConeTermProdIso ((cochainLinearDualMap φ).app M) i).hom
      ((cochainLinearDualConeShiftTermIso φ M i).hom f)).1 =
      inrX φ (0 - (i + 1)) ≫ f := by
  simp only [CochainComplex.shiftFunctor_obj_X']
  change ((mappingConeTermProdIso ((cochainLinearDualMap φ).app M) i).hom
    ((mappingConeTermProdIso ((cochainLinearDualMap φ).app M) i).inv _)).1 = _
  rw [ModuleCat.hom_inv_apply]
  rfl

/-- The second comparison coordinate is the negative old source restriction. -/
lemma cochainLinearDualConeShiftTermIso_snd (M : ModuleCat.{u} R) (i : ℤ)
    (f : (((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M)⟦(1 : ℤ)⟧).X i) :
    ((mappingConeTermProdIso ((cochainLinearDualMap φ).app M) i).hom
      ((cochainLinearDualConeShiftTermIso φ M i).hom f)).2 =
      -(inlX φ (0 - i) (0 - (i + 1)) (by change 0 - (i + 1) + 1 = 0 - i; omega) ≫ f) := by
  simp only [CochainComplex.shiftFunctor_obj_X']
  change ((mappingConeTermProdIso ((cochainLinearDualMap φ).app M) i).hom
    ((mappingConeTermProdIso ((cochainLinearDualMap φ).app M) i).inv _)).2 = _
  rw [ModuleCat.hom_inv_apply]
  change -(((K.XIsoOfEq (show 0 - (i + 1) + 1 = 0 - i by omega)).inv ≫
    (inlX φ (0 - (i + 1) + 1) (0 - (i + 1)) rfl ≫ f)) ≫ 𝟙 M) = _
  rw [Category.comp_id, ← Category.assoc, mappingCone_inlX_cast]

/-- The shift by one negates the reversed precomposition differential. -/
lemma cochainLinearDualShiftOne_d_apply (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (M : ModuleCat.{u} R) (i j : ℤ) (f : P.X (0 - (i + 1)) ⟶ M) :
    ((((cochainLinearDualFunctor P).obj M)⟦(1 : ℤ)⟧).d i j).hom f =
      -(P.d (0 - (j + 1)) (0 - (i + 1)) ≫ f) := by
  change (1 : ℤ).negOnePow • (P.d (0 - (j + 1)) (0 - (i + 1)) ≫ f) = _
  simp

/-- The signed term comparison commutes with the actual differentials. -/
lemma cochainLinearDualConeShiftTermIso_comm (M : ModuleCat.{u} R)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (cochainLinearDualConeShiftTermIso φ M i).hom ≫
        (CochainComplex.mappingCone ((cochainLinearDualMap φ).app M)).d i j =
      (((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M)⟦(1 : ℤ)⟧).d i j ≫
        (cochainLinearDualConeShiftTermIso φ M j).hom := by
  change i + 1 = j at hij
  subst j
  apply (cancel_mono (mappingConeTermProdIso ((cochainLinearDualMap φ).app M) (i + 1)).hom).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (mappingConeTermProdIso ((cochainLinearDualMap φ).app M) (i + 1)).hom
      ((CochainComplex.mappingCone ((cochainLinearDualMap φ).app M)).d i (i + 1)
        ((cochainLinearDualConeShiftTermIso φ M i).hom f)) =
    (mappingConeTermProdIso ((cochainLinearDualMap φ).app M) (i + 1)).hom
      ((cochainLinearDualConeShiftTermIso φ M (i + 1)).hom
        (((((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M)⟦(1 : ℤ)⟧).d
          i (i + 1)).hom f))
  apply Prod.ext
  · rw [mappingConeTermProdIso_d_fst, cochainLinearDualConeShiftTermIso_fst,
      cochainLinearDualConeShiftTermIso_fst, cochainLinearDual_d_apply,
      cochainLinearDualShiftOne_d_apply]
    change -(L.d (0 - (i + 1 + 1)) (0 - (i + 1)) ≫ inrX φ (0 - (i + 1)) ≫ f) =
      inrX φ (0 - (i + 1 + 1)) ≫
        (-(homotopyCofiber.d φ (0 - (i + 1 + 1)) (0 - (i + 1)) ≫ f))
    simp only [Preadditive.comp_neg, inrX_d_assoc]
  · rw [mappingConeTermProdIso_d_snd, cochainLinearDualConeShiftTermIso_fst,
      cochainLinearDualConeShiftTermIso_snd, cochainLinearDualConeShiftTermIso_snd,
      cochainLinearDual_d_apply, cochainLinearDualShiftOne_d_apply]
    change φ.f (0 - (i + 1)) ≫ inrX φ (0 - (i + 1)) ≫ f +
        K.d (0 - (i + 1)) (0 - i) ≫
          (-(inlX φ (0 - i) (0 - (i + 1)) (by change 0 - (i + 1) + 1 = 0 - i; omega) ≫ f)) =
      -(inlX φ (0 - (i + 1)) (0 - (i + 1 + 1))
        (by change 0 - (i + 1 + 1) + 1 = 0 - (i + 1); omega) ≫
        (-(homotopyCofiber.d φ (0 - (i + 1 + 1)) (0 - (i + 1)) ≫ f)))
    simp only [Preadditive.comp_neg, neg_neg]
    have h := congrArg (fun g => g ≫ f)
      (inlX_d φ (0 - (i + 1 + 1)) (0 - (i + 1)) (0 - i)
        (by change 0 - (i + 1 + 1) + 1 = 0 - (i + 1); omega)
        (by change 0 - (i + 1) + 1 = 0 - i; omega))
    simp only [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc] at h
    rw [h]
    exact add_comm _ _

/-- The shifted dual cone is the actual cone of the contravariant dual map. -/
def cochainLinearDualConeShiftIso (M : ModuleCat.{u} R) :
    ((cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M)⟦(1 : ℤ)⟧ ≅
      CochainComplex.mappingCone ((cochainLinearDualMap φ).app M) :=
  HomologicalComplex.Hom.isoOfComponents (cochainLinearDualConeShiftTermIso φ M)
    (cochainLinearDualConeShiftTermIso_comm φ M)

/-- Equivalently, dualizing a cone yields the reversed dual cone shifted by minus one. -/
def cochainLinearDualConeIso (M : ModuleCat.{u} R) :
    (cochainLinearDualFunctor (CochainComplex.mappingCone φ)).obj M ≅
      (CochainComplex.mappingCone ((cochainLinearDualMap φ).app M))⟦(-1 : ℤ)⟧ :=
  ((shiftFunctorCompIsoId (CochainComplex (ModuleCat.{u} R) ℤ)
    (1 : ℤ) (-1) (by omega)).app _).symm ≪≫
      (shiftFunctor _ (-1 : ℤ)).mapIso (cochainLinearDualConeShiftIso φ M)

end SerrePositivity
