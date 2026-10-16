module
public import SerrePositivity.HomologicalAlgebra.PureDerivedCartierNaturality
public import SerrePositivity.HomologicalAlgebra.DerivedSingleH0Algebra

/-! # Normalize the actual Cartier comparison on original discrete algebras -/
@[expose] public noncomputable section
universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard principalAdicQuotientAlgebra

/-- The normalized comparison of a single object is the inverse standard single-H⁰ comparison. -/
lemma normalizedPureHomologyIso_single {C : Type u} [Category.{v} C] [Abelian C]
    (i : ℤ) (M : C) :
    normalizedPureHomologyIso ((DerivedCategory.singleFunctor C i).obj M) i =
      (DerivedCategory.singleFunctor C i).mapIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso C i).app M).symm := by
  apply (normalizedPureHomologyIso_unique _ i _ _).symm
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.naturality
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C i).app M).inv
  calc
    _ = ((DerivedCategory.singleFunctorCompHomologyFunctorIso C i).app M).hom ≫
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso C i).app M).inv := by
      simp only [Functor.comp_map, Functor.id_map] at hn
      exact hn
    _ = _ := ((DerivedCategory.singleFunctorCompHomologyFunctorIso C i).app M).hom_inv_id

variable (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
local notation "A" => boundedAboveDerivedAlgebra (R := R) S

/-- Regular scalar action transfers through the original standard single-H⁰
comparison. -/
lemma singleH0_isSMulRegular (d : R) (M : ModuleCat.{u} R) (hM : IsSMulRegular M d) :
    IsSMulRegular ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj M) d := by
  let e := ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app M).toLinearEquiv
  intro x y hxy
  apply e.injective
  apply hM
  have he := congrArg e hxy
  simp only [LinearEquiv.map_smul] at he
  exact he

/-- On the original discrete algebra, normalization is the original single-H⁰ comparison. -/
lemma pureDerivedAlgebraSingleIso_single :
    letI hge : (A).X.obj.IsGE 0 := by
      change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsGE 0
      infer_instance
    letI hle : (A).X.obj.IsLE 0 := by
      change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsLE 0
      infer_instance
    pureDerivedAlgebraSingleIso R A = boundedAboveDerivedSingleFunctor.mapIso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app
        (ModuleCat.of R S)).symm := by
  let hge : (A).X.obj.IsGE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsGE 0
    infer_instance
  let hle : (A).X.obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsLE 0
    infer_instance
  apply Iso.ext
  apply InducedCategory.hom_ext
  change (normalizedPureHomologyIso
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)) 0).hom = _
  rw [normalizedPureHomologyIso_single]
  rfl

variable (d : R) (hd : IsSMulRegular R d) (hS : IsSMulRegular S d)
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (A).X.obj

/-- On a discrete ring the normalized Cartier comparison is the original standard quotient map. -/
lemma pureDerivedAlgebraCartierQuotientIso_single :
    letI hge : (A).X.obj.IsGE 0 := by
      change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsGE 0
      infer_instance
    letI hle : (A).X.obj.IsLE 0 := by
      change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsLE 0
      infer_instance
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    let eS : H ≃ₐ[R] S := derivedSingleH0AlgEquiv (R := R) S
    (pureDerivedAlgebraCartierQuotientIso R d hd A
        (singleH0_isSMulRegular R d (ModuleCat.of R S) hS)).hom ≫
        boundedAboveDerivedSingleFunctor.map
          (ModuleCat.ofHom (principalAdicReductionAlgHom R d eS.toAlgHom).toLinearMap) =
      (derivedQuotientModuleIsoOfRegular d hd (ModuleCat.of R S) hS).hom ≫
        boundedAboveDerivedSingleFunctor.map (principalAdicReductionEquiv d S).toModuleIso.hom := by
  let hge : (A).X.obj.IsGE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsGE 0
    infer_instance
  let hle : (A).X.obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsLE 0
    infer_instance
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let eS : H ≃ₐ[R] S := derivedSingleH0AlgEquiv (R := R) S
  let er : H ≅ ModuleCat.of R S :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app (ModuleCat.of R S)
  let hH := singleH0_isSMulRegular R d (ModuleCat.of R S) hS
  let qH := derivedQuotientModuleIsoOfRegular d hd H hH
  let qS := derivedQuotientModuleIsoOfRegular d hd (ModuleCat.of R S) hS
  let rH := (principalAdicReductionEquiv d H).toModuleIso.hom
  let rS := (principalAdicReductionEquiv d S).toModuleIso.hom
  let fq := ModuleCat.ofHom (principalAdicReductionMap d eS.toAlgHom)
  let U := boundedAboveDerivedSingleFunctor (R := Q)
  let BQ := boundedAboveDerivedBaseChange (q)
  have hq := derivedQuotientModuleIso_naturality (Ideal.span {d}) er.hom
    (scalarExtensionTorVanishing_principal_of_regular d hd H hH)
    (scalarExtensionTorVanishing_principal_of_regular d hd (ModuleCat.of R S) hS)
  change BQ.map (boundedAboveDerivedSingleFunctor.map er.hom) ≫ qS.hom =
    qH.hom ≫ U.map ((quotientModuleFunctor (Ideal.span {d})).map er.hom) at hq
  have hr := principalAdicReductionEquiv_naturality R d eS.toAlgHom
  change (quotientModuleFunctor (Ideal.span {d})).map er.hom ≫ rS = rH ≫ fq at hr
  have hc : BQ.map (boundedAboveDerivedSingleFunctor.map er.inv) ≫ qH.hom ≫
      U.map ((quotientModuleFunctor (Ideal.span {d})).map er.hom) = qS.hom := by
    rw [← hq, ← BQ.map_comp_assoc, ← Functor.map_comp]
    rw [Iso.inv_hom_id, (boundedAboveDerivedSingleFunctor (R := R)).map_id,
      BQ.map_id, Category.id_comp]
  change (BQ.map (pureDerivedAlgebraSingleIso R A).hom ≫ qH.hom ≫ U.map rH) ≫
      U.map (ModuleCat.ofHom (principalAdicReductionAlgHom R d eS.toAlgHom).toLinearMap) =
    qS.hom ≫ U.map rS
  rw [pureDerivedAlgebraSingleIso_single, principalAdicReductionAlgHom_toLinearMap]
  change (BQ.map (boundedAboveDerivedSingleFunctor.map er.inv) ≫ qH.hom ≫ U.map rH) ≫
      U.map fq = _
  simp only [Category.assoc]
  rw [← U.map_comp, ← hr, U.map_comp]
  rw [← Category.assoc qH.hom, ← Category.assoc, hc]

/-- The single-algebra Cartier H⁰ comparison is the original quotient augmentation on H⁰. -/
lemma pureDerivedAlgebraCartierQuotientH0Iso_single :
    letI hge : (A).X.obj.IsGE 0 := by
      change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsGE 0
      infer_instance
    letI hle : (A).X.obj.IsLE 0 := by
      change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsLE 0
      infer_instance
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    let eS : H ≃ₐ[R] S := derivedSingleH0AlgEquiv (R := R) S
    (pureDerivedAlgebraCartierQuotientH0Iso R d hd A
        (singleH0_isSMulRegular R d (ModuleCat.of R S) hS)).hom ≫
        ModuleCat.ofHom (principalAdicReductionAlgHom R d eS.toAlgHom).toLinearMap =
      (DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          (derivedQuotientModuleIsoOfRegular d hd (ModuleCat.of R S) hS).hom.hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q) 0).hom.app
          ((quotientModuleFunctor (Ideal.span {d})).obj (ModuleCat.of R S)) ≫
        (principalAdicReductionEquiv d S).toModuleIso.hom := by
  let hge : (A).X.obj.IsGE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsGE 0
    infer_instance
  let hle : (A).X.obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsLE 0
    infer_instance
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let eS : H ≃ₐ[R] S := derivedSingleH0AlgEquiv (R := R) S
  let hH := singleH0_isSMulRegular R d (ModuleCat.of R S) hS
  let qS := derivedQuotientModuleIsoOfRegular d hd (ModuleCat.of R S) hS
  let fq := ModuleCat.ofHom (principalAdicReductionAlgHom R d eS.toAlgHom).toLinearMap
  let rS := (principalAdicReductionEquiv d S).toModuleIso.hom
  let H0 := DerivedCategory.homologyFunctor (ModuleCat Q) 0
  let σ := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q) 0
  have hn := congrArg (fun k => H0.map k.hom)
    (pureDerivedAlgebraCartierQuotientIso_single R S d hd hS)
  simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at hn
  change H0.map (pureDerivedAlgebraCartierQuotientIso R d hd A hH).hom.hom ≫
      H0.map (boundedAboveDerivedSingleFunctor.map fq).hom =
    H0.map qS.hom.hom ≫ H0.map (boundedAboveDerivedSingleFunctor.map rS).hom at hn
  have hσ := σ.hom.naturality fq
  change H0.map (boundedAboveDerivedSingleFunctor.map fq).hom ≫ σ.hom.app _ =
    σ.hom.app _ ≫ fq at hσ
  change (H0.map (pureDerivedAlgebraCartierQuotientIso R d hd A hH).hom.hom ≫
      σ.hom.app _) ≫ fq = H0.map qS.hom.hom ≫ σ.hom.app _ ≫ rS
  rw [Category.assoc, ← hσ, ← Category.assoc, hn, Category.assoc]
  congr 1
  exact σ.hom.naturality rS

end SerrePositivity
