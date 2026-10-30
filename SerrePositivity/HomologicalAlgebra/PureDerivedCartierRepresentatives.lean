module
public import SerrePositivity.HomologicalAlgebra.PureDerivedCartierSingle
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientH0Normalization
public import SerrePositivity.CommutativeAlgebra.Adic.Reduction

/-! # Original representative classes under the normalized Cartier H⁰ comparison -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] HasDerivedCategory.standard principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (d : R) (S : Type u) [CommRing S] [Algebra R S]
local notation "A0" => boundedAboveDerivedAlgebra (R := R) S
set_option quotPrecheck false in
local notation "HS" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (A0).X.obj
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})

/-- The original quotient H⁰ computation, with the ordinary principal ring quotient as target. -/
def principalQuotientBaseChangeH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
        ((boundedAboveDerivedBaseChange (q)).obj (A0).X).obj ≅
      ModuleCat.of Q (S ⧸ Ideal.span {algebraMap R S d}) :=
  quotientBaseChangeH0Iso (Ideal.span {d}) (ModuleCat.of R S) ≪≫
    (principalAdicReductionEquiv d S).toModuleIso

variable (hd : IsSMulRegular R d) (hS : IsSMulRegular S d)
/-- Apply the normalized Cartier comparison, then the original H⁰ ring equivalence on quotients. -/
def normalizedSingleCartierH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
        ((boundedAboveDerivedBaseChange (q)).obj (A0).X).obj ≅
      ModuleCat.of Q (S ⧸ Ideal.span {algebraMap R S d}) := by
  let _hge : (A0).X.obj.IsGE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsGE 0
    infer_instance
  let _hle : (A0).X.obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsLE 0
    infer_instance
  letI := derivedH0CommRing A0
  letI := derivedH0Algebra A0
  let eS : HS ≃ₐ[R] S := derivedSingleH0AlgEquiv (R := R) S
  exact pureDerivedAlgebraCartierQuotientH0Iso R d hd A0
      (singleH0_isSMulRegular R d (ModuleCat.of R S) hS) ≪≫
    (principalAdicReductionAlgEquiv R d eS).toLinearEquiv.toModuleIso

/-- The normalized single-ring Cartier comparison is the original standard quotient computation. -/
lemma normalizedSingleCartierH0Iso_eq_standard :
    normalizedSingleCartierH0Iso R d S hd hS = principalQuotientBaseChangeH0Iso R d S := by
  let _hge : (A0).X.obj.IsGE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsGE 0
    infer_instance
  let _hle : (A0).X.obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsLE 0
    infer_instance
  let := derivedH0CommRing A0
  let := derivedH0Algebra A0
  let eS : HS ≃ₐ[R] S := derivedSingleH0AlgEquiv (R := R) S
  apply Iso.ext
  have h := pureDerivedAlgebraCartierQuotientH0Iso_single R S d hd hS
  have hq := derivedQuotientModuleIso_homology (Ideal.span {d}) (ModuleCat.of R S)
    (scalarExtensionTorVanishing_principal_of_regular d hd (ModuleCat.of R S) hS)
  change (DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
      (derivedQuotientModuleIsoOfRegular d hd (ModuleCat.of R S) hS).hom.hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q) 0).hom.app _ =
    (quotientBaseChangeH0Iso (Ideal.span {d}) (ModuleCat.of R S)).hom at hq
  change (pureDerivedAlgebraCartierQuotientH0Iso R d hd A0
      (singleH0_isSMulRegular R d (ModuleCat.of R S) hS)).hom ≫
      ModuleCat.ofHom (principalAdicReductionAlgHom R d eS.toAlgHom).toLinearMap =
    (quotientBaseChangeH0Iso (Ideal.span {d}) (ModuleCat.of R S)).hom ≫
      (principalAdicReductionEquiv d S).toModuleIso.hom
  rw [h, ← Category.assoc, hq]

/-- The original 1 tensor s class has its original ordinary quotient image. -/
lemma normalizedSingleCartierH0Iso_one_tmul (s : S) :
    (normalizedSingleCartierH0Iso R d S hd hS).hom
        ((boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app (ModuleCat.of R S)
          ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] s)) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R S d}) s := by
  rw [normalizedSingleCartierH0Iso_eq_standard]
  change principalAdicReductionEquiv d S
    ((quotientBaseChangeH0Iso (Ideal.span {d}) (ModuleCat.of R S)).hom _) = _
  rw [quotientBaseChangeH0Iso_one_tmul]
  exact principalAdicReductionEquiv_mkQ d S s

/-- Before identifying H⁰(single S) with S, the original class has
the corresponding original image. -/
lemma pureDerivedAlgebraCartierQuotientH0Iso_single_representative (s : S) :
    letI hge : (A0).X.obj.IsGE 0 := by
      change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsGE 0
      infer_instance
    letI hle : (A0).X.obj.IsLE 0 := by
      change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsLE 0
      infer_instance
    letI := derivedH0CommRing A0
    letI := derivedH0Algebra A0
    let eS : HS ≃ₐ[R] S := derivedSingleH0AlgEquiv (R := R) S
    (pureDerivedAlgebraCartierQuotientH0Iso R d hd A0
        (singleH0_isSMulRegular R d (ModuleCat.of R S) hS)).hom
        ((boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app (ModuleCat.of R S)
          ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] s)) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R HS d}) (eS.symm s) := by
  let _hge : (A0).X.obj.IsGE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsGE 0
    infer_instance
  let _hle : (A0).X.obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsLE 0
    infer_instance
  let := derivedH0CommRing A0
  let := derivedH0Algebra A0
  let eS : HS ≃ₐ[R] S := derivedSingleH0AlgEquiv (R := R) S
  apply (principalAdicReductionAlgEquiv R d eS).injective
  change (normalizedSingleCartierH0Iso R d S hd hS).hom
      ((boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app (ModuleCat.of R S)
        ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] s)) = _
  rw [principalAdicReductionAlgEquiv_mk, eS.apply_symm_apply]
  exact normalizedSingleCartierH0Iso_one_tmul R d S hd hS s

include hS in
/-- An original map from a discrete ring sends the standard source class
to its original Cartier image. -/
lemma pureDerivedAlgebraCartierQuotientH0Iso_single_map
    (B : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    [B.X.obj.IsGE 0] [B.X.obj.IsLE 0]
    (hB : IsSMulRegular ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj B.X.obj) d)
    (f : A0 ⟶ B) (s : S) :
    letI hge : (A0).X.obj.IsGE 0 := by
      change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsGE 0
      infer_instance
    letI hle : (A0).X.obj.IsLE 0 := by
      change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsLE 0
      infer_instance
    letI := derivedH0CommRing A0
    letI := derivedH0Algebra A0
    letI := derivedH0CommRing B
    letI := derivedH0Algebra B
    let eS : HS ≃ₐ[R] S := derivedSingleH0AlgEquiv (R := R) S
    (pureDerivedAlgebraCartierQuotientH0Iso R d hd B hB).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          (((boundedAboveDerivedBaseChange (q)).map f.hom.hom).hom)
          ((boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app (ModuleCat.of R S)
            ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] s))) =
      Ideal.Quotient.mk
        (Ideal.span {algebraMap R ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj B.X.obj) d})
        (derivedH0AlgMap f (eS.symm s)) := by
  let _hge : (A0).X.obj.IsGE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsGE 0
    infer_instance
  let _hle : (A0).X.obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsLE 0
    infer_instance
  let := derivedH0CommRing A0
  let := derivedH0Algebra A0
  let := derivedH0CommRing B
  let := derivedH0Algebra B
  let eS : HS ≃ₐ[R] S := derivedSingleH0AlgEquiv (R := R) S
  let x := (boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app (ModuleCat.of R S)
    ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] s)
  have hn := pureDerivedAlgebraCartierQuotientH0Iso_algHom_naturality R d hd
    (A := A0) (B := B) f (singleH0_isSMulRegular R d (ModuleCat.of R S) hS) hB
  have hx := congrArg (fun k => k x) hn
  change (pureDerivedAlgebraCartierQuotientH0Iso R d hd B hB).hom
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
        (((boundedAboveDerivedBaseChange (q)).map f.hom.hom).hom) x) =
    principalAdicReductionAlgHom R d (derivedH0AlgMap f)
      ((pureDerivedAlgebraCartierQuotientH0Iso R d hd A0
        (singleH0_isSMulRegular R d (ModuleCat.of R S) hS)).hom x) at hx
  dsimp only [x] at hx
  rw [pureDerivedAlgebraCartierQuotientH0Iso_single_representative R d S hd hS s,
    principalAdicReductionAlgHom_mk] at hx
  exact hx

end SerrePositivity
