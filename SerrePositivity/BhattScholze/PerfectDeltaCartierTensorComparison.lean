module
public import SerrePositivity.BhattScholze.PerfectDeltaIteratedTensorDiscrete
public import SerrePositivity.HomologicalAlgebra.PureDerivedCartierQuotient
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IteratedTensorQuotientComparison

/-! # The actual Cartier quotient as the original completed residue tensor

All objects and quotient actions are the original ones. This first comparison
is in the derived category of modules; multiplicative compatibility is separate.
-/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
  principalAdicQuotientAlgebra
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsAdicComplete (Ideal.span {(p : S)}) S]
    [IsAdicComplete (Ideal.span {(p : T)}) T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T)) (d : R) (hd : DR.IsDistinguished d)
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})
set_option quotPrecheck false in
local notation "SQ" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
set_option quotPrecheck false in
local notation "TQ" => T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
local notation "AP" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj
local notation "RES" => boundedAboveCompletedTensorAlgebra Q (p : Q) SQ TQ

/-- The original p-completed tensor of both ordinary residue factors is the actual Cartier quotient. -/
def perfectDelta_completedResidueTensorCartierIso :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (RES).X.obj ≅ (DerivedCategory.singleFunctor (ModuleCat Q) 0).obj
      (ModuleCat.of Q (C ⧸ Ideal.span {algebraMap R C d})) := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  have hpure := perfectDelta_iteratedTensor_pure p R S T DR DS DT hR hS hT hRS hRT d hd
  let hge : (AD).X.obj.IsGE 0 := hpure.1
  let hle : (AD).X.obj.IsLE 0 := hpure.2
  have hr : IsSMulRegular R d := by
    simpa only [IsSMulRegular, smul_eq_mul] using hR.distinguished_mul_injective hd
  have hs : IsSMulRegular S d := by
    intro x y hxy
    apply hS.distinguished_mul_injective (hRS.map_isDistinguished hd)
    simpa only [Algebra.smul_def] using hxy
  have ht : IsSMulRegular T d := by
    intro x y hxy
    apply hT.distinguished_mul_injective (hRT.map_isDistinguished hd)
    simpa only [Algebra.smul_def] using hxy
  have hc : IsSMulRegular C d := by
    intro x y hxy
    apply (perfectDeltaIteratedTensorH0Prism p R S T
      DR DS DT hR hS hT hRS hRT d hd).generator_regular
    change algebraMap R C d * x = algebraMap R C d * y
    simpa only [Algebra.smul_def] using hxy
  let e := (regularIteratedCompletedTensorQuotientIso R (p : R) d hr S T hs ht).symm ≪≫
    DerivedCategory.Minus.ι.mapIso (pureDerivedAlgebraCartierQuotientIso R d hr AD hc)
  have aux (c : Q) (h : (q) (p : R) = c) :
      (derivedComplexCompletionFunctor Q c).obj
          (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ).X.obj ≅
        (DerivedCategory.singleFunctor (ModuleCat Q) 0).obj
          (ModuleCat.of Q (C ⧸ Ideal.span {algebraMap R C d})) := by
    subst c
    exact e
  exact aux (p : Q) (map_natCast (q) p)

include hR hS hT hRS hRT hd in
/-- The original residue tensor is derived-discrete, with no residue flatness assumption. -/
lemma perfectDelta_completedResidueTensor_pure :
    (RES).X.obj.IsGE 0 ∧ (RES).X.obj.IsLE 0 := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let e := perfectDelta_completedResidueTensorCartierIso p R S T
    DR DS DT hR hS hT hRS hRT d hd
  have hz (i : ℤ) (hi : i ≠ 0) : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (RES).X.obj) :=
    (derivedSingleHomology_isZero _ i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso e)
  exact ⟨(DerivedCategory.isGE_iff _ _).mpr (fun i hi => hz i (by omega)),
    (DerivedCategory.isLE_iff _ _).mpr (fun i hi => hz i (by omega))⟩

/-- Actual residue-tensor H⁰ and the ordinary Cartier quotient agree as quotient-base modules. -/
def perfectDelta_completedResidueTensorCartierH0Iso :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RES).X.obj ≅
      ModuleCat.of Q (C ⧸ Ideal.span {algebraMap R C d}) := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  exact (DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (perfectDelta_completedResidueTensorCartierIso p R S T
        DR DS DT hR hS hT hRS hRT d hd) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q) 0).app _

end SerrePositivity.BhattScholze
