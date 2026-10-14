module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionDerived

/-! # 主元Koszul完備化への標準射の自然性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 全Koszul段への包含の族は係数複体の射と可換する。 -/
theorem complexPowerKoszulProductInclusion_naturality (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    f ≫ Pi.lift (fun n ↦ CochainComplex.mappingCone.inr (smulId (a ^ n) L)) =
      Pi.lift (fun n ↦ CochainComplex.mappingCone.inr (smulId (a ^ n) K)) ≫
        (complexPowerKoszulProductFunctor R a).map f := by
  apply Pi.hom_ext
  intro n
  change (f ≫ Pi.lift (fun n ↦ CochainComplex.mappingCone.inr (smulId (a ^ n) L))) ≫
      Pi.π (complexPowerKoszulStage R a L) n =
    (Pi.lift (fun n ↦ CochainComplex.mappingCone.inr (smulId (a ^ n) K)) ≫
      complexTowerProductMap R
        (K := complexPowerKoszulStage R a K) (L := complexPowerKoszulStage R a L)
        (fun n ↦ (scalarConeFunctor (a ^ n)).map f)) ≫
        Pi.π (complexPowerKoszulStage R a L) n
  erw [Category.assoc, Pi.lift_comp_π, Category.assoc,
    complexTowerProductMap_projection, ← Category.assoc, Pi.lift_comp_π]
  simp [scalarConeFunctor, CochainComplex.mappingCone.inr,
    homotopyCofiber.mapArrowHom, homotopyCofiber.inr_desc]

/-- 複体から完備化候補への標準射は自然である。 -/
@[reassoc] theorem complexCompletionUnit_naturality (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    f ≫ complexCompletionUnit R a L =
      complexCompletionUnit R a K ≫ (complexCompletionFunctor R a).map f := by
  change f ≫ complexCompletionUnit R a L = complexCompletionUnit R a K ≫
    (((cochainMappingConeFunctor R).map
      ((complexPowerKoszulDifferenceFunctor R a).map f))⟦(-1 : ℤ)⟧')
  apply (Cocycle.equivHomShift (K := K)
    (L := CochainComplex.mappingCone
      (complexTowerDifference R (complexPowerKoszulStage R a L)
        (complexPowerKoszulTransition R a L))) (n := (-1 : ℤ))).injective
  rw [Cocycle.equivHomShift_comp (n := (-1 : ℤ)),
    Cocycle.equivHomShift_comp_shift (n := (-1 : ℤ))]
  apply Subtype.ext
  simp only [complexCompletionUnit, complexTowerCompatibleLift,
    complexTowerHomotopyLimitLift, Cocycle.precomp, Cocycle.postcomp,
    Cocycle.mk_coe]
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp only [CochainComplex.mappingCone.liftCocycle_coe, Cocycle.ofHom_coe,
    CochainComplex.mappingCone.liftCochain, Cochain.zero_comp, add_zero]
  rw [Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [cochainMappingConeFunctor_inl]
  simp only [← Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
  exact congrArg (fun g ↦ (Cochain.ofHom g).comp _ _)
    (complexPowerKoszulProductInclusion_naturality R a f)

/-- 複体上の標準射を自然変換としてまとめる。 -/
def complexCompletionUnitNatTrans (a : R) :
    𝟭 (CochainComplex (ModuleCat.{u} R) ℤ) ⟶ complexCompletionFunctor R a where
  app := complexCompletionUnit R a
  naturality {_K _L} f := complexCompletionUnit_naturality R a f

/-- 標準射の実導来像。始域はまだ複体の圏である。 -/
def complexCompletionUnitDerivedInput (a : R) :
    DerivedCategory.Q ⟶ complexCompletionFunctor R a ⋙ DerivedCategory.Q where
  app K := complexCompletionUnitObject R a K
  naturality {K L} f := by
    change DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (complexCompletionUnit R a L) =
      DerivedCategory.Q.map (complexCompletionUnit R a K) ≫
        DerivedCategory.Q.map ((complexCompletionFunctor R a).map f)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      complexCompletionUnit_naturality]

/-- 実導来圏上の主元Koszul完備化候補への標準自然変換。 -/
def derivedComplexCompletionUnit (a : R) :
    𝟭 (ConcreteDerivedCategory R) ⟶ derivedComplexCompletionFunctor R a := by
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
      DerivedCategory.Q (𝟭 (ConcreteDerivedCategory R)) := ⟨Functor.rightUnitor _⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (complexCompletionFunctor R a ⋙ DerivedCategory.Q) (derivedComplexCompletionFunctor R a) :=
    ⟨derivedComplexCompletionComparison R a⟩
  exact Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _ _ _ _
    (complexCompletionUnitDerivedInput R a)

/-- 導来圏の標準射と、複体の具体的標準射の比較図式。 -/
@[reassoc] theorem derivedComplexCompletionUnit_comparison (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedComplexCompletionUnit R a).app (DerivedCategory.Q.obj K) ≫
      (derivedComplexCompletionComparison R a).hom.app K =
        complexCompletionUnitObject R a K := by
  simp [derivedComplexCompletionUnit, Localization.liftNatTrans_app,
    Localization.Lifting.iso, complexCompletionUnitDerivedInput]

end SerrePositivity.DerivedCompletion
