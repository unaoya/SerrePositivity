module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IteratedTensorCartierLinearComparison
public import SerrePositivity.HomologicalAlgebra.DerivedTensorCartierProducts

/-! # The original linear iterated Cartier comparison on complete pure tensor classes -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
  principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (a d : R) (hd : IsSMulRegular R d)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "X" => boundedAboveDerivedTensorAlgebra (R := R) S T
local notation "AP" => boundedAboveCompletedTensorAlgebra R a S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})
set_option quotPrecheck false in
local notation "SQ" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
set_option quotPrecheck false in
local notation "TQ" => T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
set_option quotPrecheck false in
local notation "CQ" => C ⧸ Ideal.span {algebraMap R C d}
local notation "RX" => boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ
set_option quotPrecheck false in
local notation "RC" => (boundedAboveCompletionCommMonFunctor Q ((q) a)).obj RX

/-- The original linear comparison sends completed pure tensors to their original factor product. -/
lemma iteratedCompletedTensorCartierH0Iso_unit_tmul
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0) (s : S) (t : T) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI := derivedH0CommRing RX
    letI := derivedH0Algebra RX
    let eQ : (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RX).X.obj ≃ₐ[Q]
        SQ ⊗[Q] TQ := derivedTensorH0AlgEquiv (R := Q) SQ TQ
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj)
          (eQ.symm
            (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (Ideal.span {d})) s ⊗ₜ[Q]
              Ideal.Quotient.mk (Ideal.map (algebraMap R T) (Ideal.span {d})) t))) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
          (iteratedTensorH0LeftAlgHom R a d S T s) *
        Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
          (iteratedTensorH0RightAlgHom R a d S T t) := by
  let : (AD).X.obj.IsGE 0 := hpure.1
  let : (AD).X.obj.IsLE 0 := hpure.2
  let := derivedH0CommRing X
  let := derivedH0Algebra X
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let := derivedH0CommRing RX
  let := derivedH0Algebra RX
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) T)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) T)
  let H0 := DerivedCategory.homologyFunctor (ModuleCat Q) 0
  let eQ : H0.obj (RX).X.obj ≃ₐ[Q] SQ ⊗[Q] TQ :=
    derivedTensorH0AlgEquiv (R := Q) SQ TQ
  let z := (derivedTensorQuotientBaseChangeH0Iso (Ideal.span {d}) S T hS hT).inv
    ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] (s ⊗ₜ[R] t))
  have hclass : eQ.symm
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (Ideal.span {d})) s ⊗ₜ[Q]
          Ideal.Quotient.mk (Ideal.map (algebraMap R T) (Ideal.span {d})) t) =
      H0.map (derivedTensorQuotientAlgebraIso (Ideal.span {d}) S T hS hT).hom.hom z := by
    apply eQ.injective
    rw [eQ.apply_symm_apply]
    exact (derivedTensorQuotientAlgebraIso_homology_tmul (Ideal.span {d}) S T hS hT s t).symm
  let u : X ⟶ AD := boundedAboveCompletionAlgebraUnit R a X ≫
    boundedAboveCompletionAlgebraUnit R d AP
  let u0 : (X).X ⟶ (AD).X := u.hom.hom
  have hu : u0 = (boundedAboveDerivedCompletionUnit R a).app (X).X ≫
      (boundedAboveDerivedCompletionUnit R d).app (AP).X := by
    change (boundedAboveCompletionAlgebraUnit R a X).hom.hom ≫
      (boundedAboveCompletionAlgebraUnit R d AP).hom.hom = _
    rw [boundedAboveCompletionAlgebraUnit_hom, boundedAboveCompletionAlgebraUnit_hom]
  have hU := congrArg (fun f => (pureDerivedAlgebraCartierQuotientH0Iso R d hd AD hC).hom
    (H0.map (((boundedAboveDerivedBaseChange (q)).map f).hom) z)) hu
  have h2 := pureDerivedAlgebraCartierQuotientH0Iso_tensor_representative_mul
    R d hd S T AD hS hT hC u s t
  have hright := hU.symm.trans h2
  simp only [u, iteratedTensorH0LeftAlgHom, iteratedTensorH0RightAlgHom,
    boundedAboveCompletedTensorAlgebraLeft, boundedAboveCompletedTensorAlgebraRight,
    Category.assoc, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] at hright ⊢
  have h1 := iteratedCompletedTensorCartierH0Iso_units R a d hd S T hS hT hC hpure z
  have hpre := congrArg (fun v =>
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom
      (H0.map ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj) v)) hclass
  exact hpre.trans (h1.trans hright)

/-- The original linear Cartier iso is the standard algebra extension on the same H⁰ rings. -/
lemma iteratedCompletedTensorCartierH0Iso_eq_algHom
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (hp :
      letI := derivedH0CommRing AD
      letI := derivedH0Algebra AD
      letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
      IsModuleComplete Q ((q) a) (ModuleCat.of Q CQ)) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RX
    letI := derivedH0Algebra RX
    letI := derivedH0CommRing RC
    letI := derivedH0Algebra RC
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom.hom =
      (iteratedTensorCartierCompletedAlgHom R a d S T hp).toLinearMap := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let : Algebra Q CQ := principalAdicQuotientAlgebra d C
  let := derivedH0CommRing RX
  let := derivedH0Algebra RX
  let := derivedH0CommRing RC
  let := derivedH0Algebra RC
  let H0 := DerivedCategory.homologyFunctor (ModuleCat Q) 0
  let eQ : H0.obj (RX).X.obj ≃ₐ[Q] SQ ⊗[Q] TQ :=
    derivedTensorH0AlgEquiv (R := Q) SQ TQ
  let l : H0.obj (RC).X.obj →ₗ[Q] CQ :=
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom.hom
  let k : H0.obj (RC).X.obj →ₐ[Q] CQ :=
    iteratedTensorCartierCompletedAlgHom R a d S T hp
  let j : H0.obj (RX).X.obj →ₐ[Q] H0.obj (RC).X.obj :=
    derivedH0AlgMap (boundedAboveCompletionAlgebraUnit Q ((q) a) RX)
  have hj (v : H0.obj (RX).X.obj) :
      j v = H0.map ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj) v :=
    completionH0AlgebraUnit_apply Q ((q) a) RX v
  have hext : (l.comp j.toLinearMap).comp eQ.symm.toLinearMap =
      (k.toLinearMap.comp j.toLinearMap).comp eQ.symm.toLinearMap := by
    apply TensorProduct.ext'
    intro sq tq
    refine Quotient.inductionOn' sq (fun s => ?_)
    refine Quotient.inductionOn' tq (fun t => ?_)
    let v := eQ.symm
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (Ideal.span {d})) s ⊗ₜ[Q]
        Ideal.Quotient.mk (Ideal.map (algebraMap R T) (Ideal.span {d})) t)
    have hL : l (j v) =
        Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
            (iteratedTensorH0LeftAlgHom R a d S T s) *
          Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
            (iteratedTensorH0RightAlgHom R a d S T t) := by
      exact (congrArg l (hj v)).trans
        (iteratedCompletedTensorCartierH0Iso_unit_tmul R a d hd S T hS hT hC hpure s t)
    have hK : k (j v) =
        Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
            (iteratedTensorH0LeftAlgHom R a d S T s) *
          Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
            (iteratedTensorH0RightAlgHom R a d S T t) := by
      change iteratedTensorCartierCompletedAlgHom R a d S T hp
        (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit Q ((q) a) RX) v) = _
      rw [iteratedTensorCartierCompletedAlgHom_unit]
      change iteratedTensorCartierTensorAlgHom R a d S T (eQ (eQ.symm _)) = _
      rw [eQ.apply_symm_apply, iteratedTensorCartierTensorAlgHom_tmul]
    exact hL.trans hK.symm
  let hle : (RX).X.obj.IsLE 0 := by
    change ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of Q SQ)).obj
      (ModuleCat.of Q TQ)).IsLE 0
    infer_instance
  change l = k.toLinearMap
  apply completionH0_linear_ext Q ((q) a) RX CQ hp
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hext (eQ x)
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, AlgHom.toLinearMap_apply,
    AlgEquiv.symm_apply_apply] at hx
  exact hx

/-- The standard completed residue tensor map is an algebra iso on the original H⁰ rings. -/
def iteratedTensorCartierCompletedAlgEquiv
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (hp :
      letI := derivedH0CommRing AD
      letI := derivedH0Algebra AD
      letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
      IsModuleComplete Q ((q) a) (ModuleCat.of Q CQ)) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RC
    letI := derivedH0Algebra RC
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RC).X.obj ≃ₐ[Q] CQ := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
  letI := derivedH0CommRing RC
  letI := derivedH0Algebra RC
  let eL := iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure
  let k := iteratedTensorCartierCompletedAlgHom R a d S T hp
  have he := iteratedCompletedTensorCartierH0Iso_eq_algHom R a d hd S T hS hT hC hpure hp
  have hefun : (fun x => eL.hom x) = (fun x => k x) :=
    funext (fun x => LinearMap.congr_fun he x)
  have hb : Function.Bijective k :=
    (congrArg Function.Bijective hefun).mp eL.toLinearEquiv.bijective
  exact AlgEquiv.ofBijective k hb

/-- Its algebra map is precisely the original standard extension. -/
lemma iteratedTensorCartierCompletedAlgEquiv_toAlgHom
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (hp :
      letI := derivedH0CommRing AD
      letI := derivedH0Algebra AD
      letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
      IsModuleComplete Q ((q) a) (ModuleCat.of Q CQ)) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RC
    letI := derivedH0Algebra RC
    (iteratedTensorCartierCompletedAlgEquiv R a d hd S T hS hT hC hpure hp).toAlgHom =
      iteratedTensorCartierCompletedAlgHom R a d S T hp := by
  rfl

/-- Its underlying linear equivalence is the original Cartier H⁰ comparison. -/
lemma iteratedTensorCartierCompletedAlgEquiv_toLinearEquiv
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (hp :
      letI := derivedH0CommRing AD
      letI := derivedH0Algebra AD
      letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
      IsModuleComplete Q ((q) a) (ModuleCat.of Q CQ)) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RC
    letI := derivedH0Algebra RC
    (iteratedTensorCartierCompletedAlgEquiv R a d hd S T hS hT hC hpure hp).toLinearEquiv =
      (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).toLinearEquiv := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let : Algebra Q CQ := principalAdicQuotientAlgebra d C
  let := derivedH0CommRing RC
  let := derivedH0Algebra RC
  apply LinearEquiv.ext
  intro x
  exact (LinearMap.congr_fun
    (iteratedCompletedTensorCartierH0Iso_eq_algHom R a d hd S T hS hT hC hpure hp) x).symm

end SerrePositivity.DerivedCompletion
