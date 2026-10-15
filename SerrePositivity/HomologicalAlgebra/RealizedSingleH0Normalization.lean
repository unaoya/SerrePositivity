module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra

/-! # The chain realization uses the canonical single-object H⁰ comparison -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Extension of a single chain complex preserves its canonical homology coefficient. -/
lemma extendChainSingle_homology_normalization (M : ModuleCat.{u} R) :
    homologyMap (extendSingleIso embUp M 0 0 (by simp [embUp])).inv 0 ≫
      (((single (ModuleCat R) (.down ℕ) 0).obj M).extendHomologyIso embUp
        (show embUp.f 0 = 0 by simp [embUp])).hom ≫
        (singleObjHomologySelfIso (.down ℕ) 0 M).hom =
      (singleObjHomologySelfIso (.up ℤ) 0 M).hom := by
  apply (cancel_epi (((single (ModuleCat R) (.up ℤ) 0).obj M).homologyπ 0)).mp
  rw [homologyπ_naturality_assoc, homologyπ_extendHomologyIso_hom_assoc,
    homologyπ_singleObjHomologySelfIso_hom, homologyπ_singleObjHomologySelfIso_hom]
  simp only [singleObjCyclesSelfIso_hom]
  rw [extendCyclesIso_hom_iCycles_assoc, cyclesMap_i_assoc]
  simp only [extendSingleIso_inv_f, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The existing chain-realization H⁰ comparison is precisely the canonical single comparison. -/
theorem realizedSingleH0Iso_hom_eq_standard (M : ModuleCat.{u} R) :
    (realizedSingleH0Iso R).hom.app M =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app M := by
  simp only [Functor.comp_obj, Functor.id_obj, realizedSingleH0Iso,
    chainDerivedRealizationSingleNatIso, chainDerivedRealizationComplexNatIso,
    ComplexShape.Embedding.extendHomotopyFunctorFactors, Functor.isoWhiskerRight_refl,
    Iso.refl_trans, Functor.isoWhiskerLeft_trans, Functor.isoWhiskerLeft_twice,
    extendChainSingleNatIso, Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.trans_symm,
    Iso.symm_symm_eq, Functor.isoWhiskerRight_trans, chainDerivedRealizationHomologyIso,
    Int.cast_ofNat_Int, Int.neg_zero, extendHomotopyChainHomologyIso,
    homotopyChainSingleHomologyIso, Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_twice, Functor.isoWhiskerLeft_inv,
    Iso.symm_inv, Functor.isoWhiskerLeft_hom, Quotient.natIsoLift_hom, Quotient.natTransLift,
    Iso.refl_hom, NatTrans.comp_app, ComplexShape.Embedding.extendFunctor_obj, NatTrans.id_app,
    Functor.associator_hom_app, homologyFunctor_obj, Functor.whiskerLeft_app, Category.id_comp,
    Category.assoc, DerivedCategory.Q_obj_single_obj, Functor.whiskerRight_app,
    NatIso.ofComponents_inv_app, Functor.comp_map, Functor.associator_inv_app,
    CategoryTheory.Functor.map_id, HomotopyCategory.quotient_obj_as,
    homologyFunctorSingleIso_hom_app, Iso.inv_hom_id_app_assoc, NatTrans.naturality_map_assoc,
    DerivedCategory.singleFunctorCompHomologyFunctorIso, SingleFunctors.evaluation_obj,
    SingleFunctors.postcomp_functor, Functor.mapIso_hom, SingleFunctors.evaluation_map,
    DerivedCategory.singleFunctorsPostcompQIso_hom_hom, Functor.whiskerRight_id']
  try simp only [Category.id_comp]
  change (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app
        ((single (ModuleCat R) (.up ℤ) 0).obj M)) ≫
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat R) (.up ℤ)).map
        ((extendChainSingleNatIso R).inv.app M))) ≫
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat R) 0).hom.app
      ((HomotopyCategory.quotient (ModuleCat R) (.up ℤ)).obj
        (((single (ModuleCat R) (.down ℕ) 0).obj M).extend embUp)) ≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat R) (.up ℤ) 0).hom.app
      (((single (ModuleCat R) (.down ℕ) 0).obj M).extend embUp) ≫
    (((single (ModuleCat R) (.down ℕ) 0).obj M).extendHomologyIso embUp
      (show embUp.f 0 = 0 by simp [embUp])).hom ≫
    (singleObjHomologySelfIso (.down ℕ) 0 M).hom = _
  rw [DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc]
  have hn := congrArg (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    (DerivedCategory.quotientCompQhIso_hom_naturality
      ((extendChainSingleNatIso R).inv.app M))
  simp only [CategoryTheory.Functor.map_comp] at hn
  erw [reassoc_of% hn]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]
  rw [show homologyMap ((extendChainSingleNatIso R).inv.app M) 0 ≫
      (((single (ModuleCat R) (.down ℕ) 0).obj M).extendHomologyIso embUp
        (show embUp.f 0 = 0 by simp [embUp])).hom ≫
        (singleObjHomologySelfIso (.down ℕ) 0 M).hom =
        (singleObjHomologySelfIso (.up ℤ) 0 M).hom from
    extendChainSingle_homology_normalization M]



/-- The comparison natural isomorphisms coincide, including their inverse maps. -/
theorem realizedSingleH0Iso_eq_standard :
    realizedSingleH0Iso R =
      DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0 := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  exact realizedSingleH0Iso_hom_eq_standard M

/-- The H⁰ algebra comparison has exactly the existing tensor H⁰ comparison as its function. -/
theorem derivedTensorH0AlgHom_eq_existing
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    derivedTensorH0AlgHom S T x =
      (boundedAboveDerivedTensorModuleH0NatIso (ModuleCat.of R S)).hom.app
        (ModuleCat.of R T) x := by
  rw [derivedTensorH0AlgHom_apply, ← realizedSingleH0Iso_hom_eq_standard]
  exact congrArg (fun k ↦ k.hom x)
    (boundedAboveDerivedTensorModuleAugmentation_homology (ModuleCat.of R S) (ModuleCat.of R T))

end SerrePositivity
