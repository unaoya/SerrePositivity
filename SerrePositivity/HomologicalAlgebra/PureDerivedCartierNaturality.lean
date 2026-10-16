module
public import SerrePositivity.HomologicalAlgebra.PureDerivedCartierQuotient
public import SerrePositivity.CommutativeAlgebra.PrincipalAdicReductionAlgebra

/-! # Naturality of the normalized original Cartier quotient comparison -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R]

/-- The standard module-to-ring quotient comparison respects the original algebra map. -/
lemma principalAdicReductionEquiv_naturality (d : R)
    {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) :
    (quotientModuleFunctor (Ideal.span {d})).map (ModuleCat.ofHom f.toLinearMap) ≫
        (principalAdicReductionEquiv d T).toModuleIso.hom =
      (principalAdicReductionEquiv d S).toModuleIso.hom ≫
        ModuleCat.ofHom (principalAdicReductionMap d f) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change principalAdicReductionEquiv d T (adicReductionMap (Ideal.span {d}) f.toLinearMap x) =
    principalAdicReductionMap d f (principalAdicReductionEquiv d S x)
  simp only [principalAdicReductionMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

/-- The original normalized pure-object comparison, in the bounded-above category. -/
def pureDerivedAlgebraSingleIso
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    [A.X.obj.IsGE 0] [A.X.obj.IsLE 0] :
    A.X ≅ boundedAboveDerivedSingleFunctor.obj
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :=
  ObjectProperty.isoMk _ (normalizedPureHomologyIso A.X.obj 0)

/-- Normalization respects actual algebra morphisms through their unchanged H⁰ map. -/
lemma pureDerivedAlgebraSingleIso_naturality
    {A B : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))}
    [A.X.obj.IsGE 0] [A.X.obj.IsLE 0] [B.X.obj.IsGE 0] [B.X.obj.IsLE 0] (f : A ⟶ B) :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing B
    letI := derivedH0Algebra B
    f.hom.hom ≫ (pureDerivedAlgebraSingleIso R B).hom =
      (pureDerivedAlgebraSingleIso R A).hom ≫
        boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (derivedH0AlgMap f).toLinearMap) := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing B
  let := derivedH0Algebra B
  have he : (DerivedCategory.homologyFunctor (ModuleCat R) 0).map f.hom.hom.hom =
      ModuleCat.ofHom (derivedH0AlgMap f).toLinearMap := by
    ext x
    exact (derivedH0AlgMap_apply f x).symm
  apply InducedCategory.hom_ext
  change f.hom.hom.hom ≫ (normalizedPureHomologyIso B.X.obj 0).hom =
    (normalizedPureHomologyIso A.X.obj 0).hom ≫
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map _
  rw [← he]
  exact normalizedPureHomologyIso_naturality (X := A.X.obj) (Y := B.X.obj) 0 f.hom.hom.hom

variable (d : R) (hd : IsSMulRegular R d)
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})

set_option maxHeartbeats 800000 in
-- This comparison unfolds the four original H⁰ algebra instances and three composed derived isomorphisms.
/-- The actual Cartier comparison preserves the original algebra map on both quotient sides. -/
lemma pureDerivedAlgebraCartierQuotientIso_naturality
    {A B : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))}
    [A.X.obj.IsGE 0] [A.X.obj.IsLE 0] [B.X.obj.IsGE 0] [B.X.obj.IsLE 0]
    (f : A ⟶ B)
    (hA : IsSMulRegular ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) d)
    (hB : IsSMulRegular ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj B.X.obj) d) :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing B
    letI := derivedH0Algebra B
    (boundedAboveDerivedBaseChange (q)).map f.hom.hom ≫
        (pureDerivedAlgebraCartierQuotientIso R d hd B hB).hom =
      (pureDerivedAlgebraCartierQuotientIso R d hd A hA).hom ≫
        boundedAboveDerivedSingleFunctor.map
          (ModuleCat.ofHom (principalAdicReductionMap d (derivedH0AlgMap f))) := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing B
  let := derivedH0Algebra B
  let fH := ModuleCat.ofHom (derivedH0AlgMap f).toLinearMap
  have hn := pureDerivedAlgebraSingleIso_naturality R f
  have hq := derivedQuotientModuleIso_naturality (Ideal.span {d}) fH
    (scalarExtensionTorVanishing_principal_of_regular d hd _ hA)
    (scalarExtensionTorVanishing_principal_of_regular d hd _ hB)
  change (boundedAboveDerivedBaseChange (q)).map (boundedAboveDerivedSingleFunctor.map fH) ≫
      (derivedQuotientModuleIsoOfRegular d hd _ hB).hom =
    (derivedQuotientModuleIsoOfRegular d hd _ hA).hom ≫
      boundedAboveDerivedSingleFunctor.map ((quotientModuleFunctor (Ideal.span {d})).map fH) at hq
  have hr := principalAdicReductionEquiv_naturality R d (derivedH0AlgMap f)
  change (boundedAboveDerivedBaseChange (q)).map f.hom.hom ≫
      ((boundedAboveDerivedBaseChange (q)).map (pureDerivedAlgebraSingleIso R B).hom ≫
        (derivedQuotientModuleIsoOfRegular d hd _ hB).hom ≫
        boundedAboveDerivedSingleFunctor.map (principalAdicReductionEquiv d _).toModuleIso.hom) =
    ((boundedAboveDerivedBaseChange (q)).map (pureDerivedAlgebraSingleIso R A).hom ≫
        (derivedQuotientModuleIsoOfRegular d hd _ hA).hom ≫
        boundedAboveDerivedSingleFunctor.map (principalAdicReductionEquiv d _).toModuleIso.hom) ≫ _
  rw [← Category.assoc, ← Functor.map_comp, hn, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((boundedAboveDerivedBaseChange (q)).map
    (boundedAboveDerivedSingleFunctor.map fH)), hq]
  simp only [Category.assoc]
  congr 2
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg boundedAboveDerivedSingleFunctor.map hr

/-- The original H⁰ Cartier comparison has the same quotient-map naturality square. -/
lemma pureDerivedAlgebraCartierQuotientH0Iso_naturality
    {A B : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))}
    [A.X.obj.IsGE 0] [A.X.obj.IsLE 0] [B.X.obj.IsGE 0] [B.X.obj.IsLE 0]
    (f : A ⟶ B)
    (hA : IsSMulRegular ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) d)
    (hB : IsSMulRegular ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj B.X.obj) d) :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing B
    letI := derivedH0Algebra B
    (DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {d})) 0).map
        (((boundedAboveDerivedBaseChange (q)).map f.hom.hom).hom) ≫
        (pureDerivedAlgebraCartierQuotientH0Iso R d hd B hB).hom =
      (pureDerivedAlgebraCartierQuotientH0Iso R d hd A hA).hom ≫
        ModuleCat.ofHom (principalAdicReductionMap d (derivedH0AlgMap f)) := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing B
  let := derivedH0Algebra B
  let H0 := DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {d})) 0
  let fq := ModuleCat.ofHom (principalAdicReductionMap d (derivedH0AlgMap f))
  have hn := congrArg (fun g => H0.map g.hom)
    (pureDerivedAlgebraCartierQuotientIso_naturality R d hd f hA hB)
  simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at hn
  change H0.map (((boundedAboveDerivedBaseChange (q)).map f.hom.hom).hom) ≫
      (H0.map (pureDerivedAlgebraCartierQuotientIso R d hd B hB).hom.hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat (R ⧸ Ideal.span {d})) 0).hom.app _) =
    (H0.map (pureDerivedAlgebraCartierQuotientIso R d hd A hA).hom.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat (R ⧸ Ideal.span {d})) 0).hom.app _) ≫ fq
  rw [← Category.assoc, hn, Category.assoc]
  rw [Category.assoc]
  congr 1
  exact (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat (R ⧸ Ideal.span {d})) 0).hom.naturality fq

/-- The H⁰ square uses the original induced quotient algebra homomorphism. -/
lemma pureDerivedAlgebraCartierQuotientH0Iso_algHom_naturality
    {A B : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))}
    [A.X.obj.IsGE 0] [A.X.obj.IsLE 0] [B.X.obj.IsGE 0] [B.X.obj.IsLE 0]
    (f : A ⟶ B)
    (hA : IsSMulRegular ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) d)
    (hB : IsSMulRegular ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj B.X.obj) d) :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing B
    letI := derivedH0Algebra B
    (DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {d})) 0).map
        (((boundedAboveDerivedBaseChange (q)).map f.hom.hom).hom) ≫
        (pureDerivedAlgebraCartierQuotientH0Iso R d hd B hB).hom =
      (pureDerivedAlgebraCartierQuotientH0Iso R d hd A hA).hom ≫
        ModuleCat.ofHom (principalAdicReductionAlgHom R d (derivedH0AlgMap f)).toLinearMap := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing B
  let := derivedH0Algebra B
  simpa only [principalAdicReductionAlgHom_toLinearMap] using
    pureDerivedAlgebraCartierQuotientH0Iso_naturality R d hd f hA hB

end SerrePositivity
