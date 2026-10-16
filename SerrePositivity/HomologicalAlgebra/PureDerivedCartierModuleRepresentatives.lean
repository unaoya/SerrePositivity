module
public import SerrePositivity.HomologicalAlgebra.PureDerivedCartierNaturality
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientH0Normalization

/-! # Cartier representative classes from arbitrary discrete source modules -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] HasDerivedCategory.standard principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (d : R) (hd : IsSMulRegular R d)
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    [A.X.obj.IsGE 0] [A.X.obj.IsLE 0]
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})

/-- Normalize the target, then use the original quotient H⁰ computation on its actual module. -/
lemma pureDerivedAlgebraCartierQuotientH0Iso_hom_normalized
    (hA : IsSMulRegular H d) :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    (pureDerivedAlgebraCartierQuotientH0Iso R d hd A hA).hom =
      (DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          (((boundedAboveDerivedBaseChange (q)).map (pureDerivedAlgebraSingleIso R A).hom).hom) ≫
        (quotientBaseChangeH0Iso (Ideal.span {d}) H).hom ≫
        (principalAdicReductionEquiv d H).toModuleIso.hom := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let H0 := DerivedCategory.homologyFunctor (ModuleCat Q) 0
  let σ := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q) 0
  let e := (principalAdicReductionEquiv d H).toModuleIso
  have hn := σ.hom.naturality e.hom
  change H0.map ((DerivedCategory.singleFunctor (ModuleCat Q) 0).map e.hom) ≫
      σ.hom.app _ = σ.hom.app _ ≫ e.hom at hn
  have hb := derivedQuotientModuleIso_homology (Ideal.span {d}) H
    (scalarExtensionTorVanishing_principal_of_regular d hd H hA)
  change H0.map (derivedQuotientModuleIsoOfRegular d hd H hA).hom.hom ≫
      σ.hom.app _ = (quotientBaseChangeH0Iso (Ideal.span {d}) H).hom at hb
  simp only [pureDerivedAlgebraCartierQuotientH0Iso, pureDerivedAlgebraCartierQuotientIso,
    Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  change H0.map (((boundedAboveDerivedBaseChange (q)).map
      (pureDerivedAlgebraSingleIso R A).hom).hom) ≫
      H0.map (derivedQuotientModuleIsoOfRegular d hd H hA).hom.hom ≫
      H0.map ((DerivedCategory.singleFunctor (ModuleCat Q) 0).map e.hom) ≫
      σ.hom.app _ = _
  rw [hn]
  have hbe := congrArg (fun f => H0.map (((boundedAboveDerivedBaseChange (q)).map
    (pureDerivedAlgebraSingleIso R A).hom).hom) ≫ f ≫ e.hom) hb
  simp only [Category.assoc] at hbe
  exact hbe

/-- Discrete source classes retain their Cartier image
without source regularity or Tor assumptions. -/
lemma pureDerivedAlgebraCartierQuotientH0Iso_module_representative
    (hA : IsSMulRegular H d) (M : ModuleCat.{u} R) (g : M ⟶ H) (m : M) :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    (pureDerivedAlgebraCartierQuotientH0Iso R d hd A hA).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          (((boundedAboveDerivedBaseChange (q)).map
            (boundedAboveDerivedSingleFunctor.map g ≫ (pureDerivedAlgebraSingleIso R A).inv)).hom)
          ((boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app M
            ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] m))) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R H d}) (g m) := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let H0 := DerivedCategory.homologyFunctor (ModuleCat Q) 0
  let n := pureDerivedAlgebraSingleIso R A
  let x := (boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app M
    ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] m)
  have hc :
      (((boundedAboveDerivedBaseChange (q)).map
        (boundedAboveDerivedSingleFunctor.map g ≫ n.inv)).hom) ≫
        (((boundedAboveDerivedBaseChange (q)).map n.hom).hom) =
      (((boundedAboveDerivedBaseChange (q)).map (boundedAboveDerivedSingleFunctor.map g)).hom) := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, ← Functor.map_comp,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hcx := congrArg (fun f => H0.map f x) hc
  rw [Functor.map_comp] at hcx
  simp only [ModuleCat.comp_apply] at hcx
  let β := boundedAboveDerivedBaseChangeModuleH0Iso (q)
  let bM := β.app M
  let bH := β.app H
  have hn := β.hom.naturality g
  change H0.map (((boundedAboveDerivedBaseChange (q)).map
      (boundedAboveDerivedSingleFunctor.map g)).hom) ≫ bH.hom =
    bM.hom ≫ (ModuleCat.extendScalars (q)).map g at hn
  have hnx := congrArg (fun f => f x) hn
  simp only [ModuleCat.comp_apply] at hnx
  change bH.hom (H0.map (((boundedAboveDerivedBaseChange (q)).map
      (boundedAboveDerivedSingleFunctor.map g)).hom) x) =
    ((ModuleCat.extendScalars (q)).map g)
      (bM.hom (bM.inv ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] m))) at hnx
  rw [ModuleCat.hom_inv_apply] at hnx
  have hxy : H0.map (((boundedAboveDerivedBaseChange (q)).map
        (boundedAboveDerivedSingleFunctor.map g)).hom) x =
      bH.inv ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] (g m)) := by
    apply bH.toLinearEquiv.injective
    change bH.hom _ = bH.hom (bH.inv _)
    rw [ModuleCat.hom_inv_apply, hnx]
    exact ModuleCat.ExtendScalars.map_tmul (q) g 1 m
  rw [pureDerivedAlgebraCartierQuotientH0Iso_hom_normalized]
  simp only [ModuleCat.comp_apply]
  change principalAdicReductionEquiv d H
    ((quotientBaseChangeH0Iso (Ideal.span {d}) H).hom
      (H0.map (((boundedAboveDerivedBaseChange (q)).map n.hom).hom)
        (H0.map (((boundedAboveDerivedBaseChange (q)).map
          (boundedAboveDerivedSingleFunctor.map g ≫ n.inv)).hom) x))) = _
  have hfinal := congrArg (fun v => principalAdicReductionEquiv d H
    ((quotientBaseChangeH0Iso (Ideal.span {d}) H).hom v)) (hcx.trans hxy)
  have hq := quotientBaseChangeH0Iso_one_tmul (Ideal.span {d}) H (g m)
  have hp := congrArg (principalAdicReductionEquiv d H) hq
  exact hfinal.trans (hp.trans (principalAdicReductionEquiv_mkQ d H (g m)))

end SerrePositivity
