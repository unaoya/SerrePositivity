module
public import SerrePositivity.HomologicalAlgebra.PureDerivedCartierModuleRepresentatives
public import SerrePositivity.HomologicalAlgebra.DerivedTensorPureFactorization
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientTensorAugmentation

/-! # Original pure tensor representatives in the unchanged Cartier quotient -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
  principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (d : R) (hd : IsSMulRegular R d)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    [A.X.obj.IsGE 0] [A.X.obj.IsLE 0]
local notation "B" => boundedAboveDerivedTensorAlgebra (R := R) S T
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})

/-- A map to a pure algebra sends the original normalized tensor class to its Cartier image. -/
lemma pureDerivedAlgebraCartierQuotientH0Iso_tensor_representative
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hA : IsSMulRegular H d) (u : B ⟶ A) (s : S) (t : T) :
    letI := derivedH0CommRing B
    letI := derivedH0Algebra B
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    let e : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (B).X.obj ≃ₐ[R] S ⊗[R] T :=
      derivedTensorH0AlgEquiv (R := R) S T
    let g : S ⊗[R] T →ₐ[R] H := (derivedH0AlgMap u).comp e.symm.toAlgHom
    (pureDerivedAlgebraCartierQuotientH0Iso R d hd A hA).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          (((boundedAboveDerivedBaseChange (q)).map u.hom.hom).hom)
          ((derivedTensorQuotientBaseChangeH0Iso (Ideal.span {d}) S T hS hT).inv
            ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] (s ⊗ₜ[R] t)))) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R H d}) (g (s ⊗ₜ[R] t)) := by
  let := derivedH0CommRing B
  let := derivedH0Algebra B
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let M := ModuleCat.of R (S ⊗[R] T)
  let H0 := DerivedCategory.homologyFunctor (ModuleCat Q) 0
  let F := boundedAboveDerivedBaseChange (q)
  let e : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (B).X.obj ≃ₐ[R] S ⊗[R] T :=
    derivedTensorH0AlgEquiv (R := R) S T
  let g : S ⊗[R] T →ₐ[R] H := (derivedH0AlgMap u).comp e.symm.toAlgHom
  let u0 : (B).X ⟶ A.X := u.hom.hom
  let α : (B).X ⟶ boundedAboveDerivedSingleFunctor.obj M :=
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom
  let f : boundedAboveDerivedSingleFunctor.obj M ⟶ A.X :=
    boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom g.toLinearMap) ≫
      (pureDerivedAlgebraSingleIso R A).inv
  have hf := derivedTensorAlgebraMap_factor_pure R S T A u
  change u0 = α ≫ f at hf
  let eq := derivedTensorQuotientBaseChangeH0Iso (Ideal.span {d}) S T hS hT
  let b := (boundedAboveDerivedBaseChangeModuleH0Iso (q)).app M
  let c := (1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] (s ⊗ₜ[R] t)
  let z := eq.inv c
  have hmap := congrArg (fun v => H0.map ((F.map v).hom) z) hf
  rw [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at hmap
  simp only [ModuleCat.comp_apply] at hmap
  let α0 : (B).X ⟶ boundedAboveDerivedSingleFunctor.obj M :=
    ObjectProperty.homMk ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R S)).app
      (ModuleCat.of R T))
  have ha : α = α0 := by
    apply InducedCategory.hom_ext
    exact boundedAboveDerivedTensorAlgebraAugmentation_hom S T
  have haug := congrArg (fun v => H0.map ((F.map v).hom) z) ha
  have hstd : H0.map ((F.map α0).hom) z = b.inv c := by
    apply b.toLinearEquiv.injective
    change eq.hom (eq.inv c) = b.hom (b.inv c)
    rw [ModuleCat.hom_inv_apply, ModuleCat.hom_inv_apply]
  have hz := haug.trans hstd
  have hv := hmap.trans (congrArg (fun v => H0.map ((F.map f).hom) v) hz)
  have hCart := congrArg (pureDerivedAlgebraCartierQuotientH0Iso R d hd A hA).hom hv
  exact hCart.trans
    (pureDerivedAlgebraCartierQuotientH0Iso_module_representative R d hd A hA M
      (ModuleCat.ofHom g.toLinearMap) (s ⊗ₜ[R] t))

/-- The actual tensor H⁰ algebra map sends pure tensors to the original two factor images. -/
lemma derivedTensorAlgebraMap_tmul (u : B ⟶ A) (s : S) (t : T) :
    letI := derivedH0CommRing B
    letI := derivedH0Algebra B
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
    letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
    letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) T)
    letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) T)
    let e : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (B).X.obj ≃ₐ[R] S ⊗[R] T :=
      derivedTensorH0AlgEquiv (R := R) S T
    let eS : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveDerivedAlgebra (R := R) S).X.obj ≃ₐ[R] S :=
      derivedSingleH0AlgEquiv (R := R) S
    let eT : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveDerivedAlgebra (R := R) T).X.obj ≃ₐ[R] T :=
      derivedSingleH0AlgEquiv (R := R) T
    ((derivedH0AlgMap u).comp e.symm.toAlgHom) (s ⊗ₜ[R] t) =
      derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T ≫ u) (eS.symm s) *
        derivedH0AlgMap (boundedAboveDerivedTensorAlgebraRight (R := R) S T ≫ u) (eT.symm t) := by
  let := derivedH0CommRing B
  let := derivedH0Algebra B
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) T)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) T)
  let e : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (B).X.obj ≃ₐ[R] S ⊗[R] T :=
    derivedTensorH0AlgEquiv (R := R) S T
  let eS : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj ≃ₐ[R] S :=
    derivedSingleH0AlgEquiv (R := R) S
  let eT : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj ≃ₐ[R] T :=
    derivedSingleH0AlgEquiv (R := R) T
  let xS := derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) (eS.symm s)
  let xT := derivedH0AlgMap (boundedAboveDerivedTensorAlgebraRight (R := R) S T) (eT.symm t)
  have hs := derivedTensorH0AlgHom_left (R := R) S T (eS.symm s)
  change e xS = (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T) (eS (eS.symm s)) at hs
  rw [eS.apply_symm_apply] at hs
  have ht := derivedTensorH0AlgHom_right (R := R) S T (eT.symm t)
  change e xT = (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T) (eT (eT.symm t)) at ht
  rw [eT.apply_symm_apply] at ht
  have he : e.symm (s ⊗ₜ[R] t) = xS * xT := by
    apply e.injective
    rw [e.apply_symm_apply, map_mul, hs, ht]
    simp only [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hl : derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T ≫ u) (eS.symm s) =
      derivedH0AlgMap u xS := by
    rw [derivedH0AlgMap_comp, AlgHom.comp_apply]
  have hr : derivedH0AlgMap (boundedAboveDerivedTensorAlgebraRight (R := R) S T ≫ u) (eT.symm t) =
      derivedH0AlgMap u xT := by
    rw [derivedH0AlgMap_comp, AlgHom.comp_apply]
  change derivedH0AlgMap u (e.symm (s ⊗ₜ[R] t)) =
    derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T ≫ u) (eS.symm s) *
      derivedH0AlgMap (boundedAboveDerivedTensorAlgebraRight (R := R) S T ≫ u) (eT.symm t)
  rw [hl, hr]
  rw [he, map_mul]

/-- The original Cartier image of a normalized pure tensor is the product of its factor images. -/
lemma pureDerivedAlgebraCartierQuotientH0Iso_tensor_representative_mul
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hA : IsSMulRegular H d) (u : B ⟶ A) (s : S) (t : T) :
    letI := derivedH0CommRing B
    letI := derivedH0Algebra B
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
    letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
    letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) T)
    letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) T)
    let eS : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveDerivedAlgebra (R := R) S).X.obj ≃ₐ[R] S :=
      derivedSingleH0AlgEquiv (R := R) S
    let eT : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveDerivedAlgebra (R := R) T).X.obj ≃ₐ[R] T :=
      derivedSingleH0AlgEquiv (R := R) T
    (pureDerivedAlgebraCartierQuotientH0Iso R d hd A hA).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          (((boundedAboveDerivedBaseChange (q)).map u.hom.hom).hom)
          ((derivedTensorQuotientBaseChangeH0Iso (Ideal.span {d}) S T hS hT).inv
            ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] (s ⊗ₜ[R] t)))) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R H d})
          (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T ≫ u) (eS.symm s)) *
        Ideal.Quotient.mk (Ideal.span {algebraMap R H d})
          (derivedH0AlgMap
            (boundedAboveDerivedTensorAlgebraRight (R := R) S T ≫ u) (eT.symm t)) := by
  let := derivedH0CommRing B
  let := derivedH0Algebra B
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) T)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) T)
  have h := pureDerivedAlgebraCartierQuotientH0Iso_tensor_representative R d hd S T A
    hS hT hA u s t
  have hm := derivedTensorAlgebraMap_tmul R S T A u s t
  have hq := congrArg (Ideal.Quotient.mk (Ideal.span {algebraMap R H d})) hm
  exact h.trans (hq.trans (map_mul (Ideal.Quotient.mk (Ideal.span {algebraMap R H d})) _ _))

end SerrePositivity
