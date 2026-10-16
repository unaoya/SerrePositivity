module
public import SerrePositivity.BhattScholze.PerfectDeltaIteratedTensorH0
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IteratedTensorCartierAlgebra

/-! # The original Cartier quotient supplies the actual completed residue-tensor algebra map -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
  principalAdicQuotientAlgebra
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T)) (d : R) (hd : DR.IsDistinguished d)
local notation "AP" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})
set_option quotPrecheck false in
local notation "CQ" => C ⧸ Ideal.span {algebraMap R C d}
set_option quotPrecheck false in
local notation "SQ" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
set_option quotPrecheck false in
local notation "TQ" => T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
local notation "RES" => boundedAboveCompletedTensorAlgebra Q (p : Q) SQ TQ

include hR hS hT hRS hRT hd in
/-- The literal original Cartier quotient is p-adically complete, with p-torsion allowed. -/
lemma perfectDelta_iteratedTensorCartier_isAdicComplete :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    IsAdicComplete (Ideal.span {(p : CQ)}) CQ := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let P := perfectDeltaIteratedTensorH0Prism p R S T DR DS DT hR hS hT hRS hRT d hd
  have hP := perfectDeltaIteratedTensorH0Prism_isPerfect p R S T
    DR DS DT hR hS hT hRS hRT d hd
  let := P.isAdicComplete_p_of_perfect hP
  exact hP.distinguished_quotient_isAdicComplete
    (perfectDeltaIteratedTensorH0Structure_distinguished p R S T
      DR DS DT hR hS hT hRS hRT d hd)

include hR hS hT hRS hRT hd in
/-- The exact quotient-base derived completeness required by the common algebra extension. -/
lemma perfectDelta_iteratedTensorCartier_isModuleComplete :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    IsModuleComplete Q ((q) (p : R)) (ModuleCat.of Q CQ) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let := perfectDelta_iteratedTensorCartier_isAdicComplete p R S T
    DR DS DT hR hS hT hRS hRT d hd
  have hc : IsModuleComplete CQ (p : CQ) (ModuleCat.of CQ CQ) :=
    isModuleComplete_of_isAdicComplete CQ (p : CQ) (ModuleCat.of CQ CQ)
  have hc' : IsModuleComplete CQ (algebraMap Q CQ (p : Q)) (ModuleCat.of CQ CQ) := by
    simpa only [map_natCast] using hc
  rw [map_natCast]
  exact (isModuleComplete_algebraMap_iff Q CQ (p : Q) CQ).mp hc'

/-- The standard residue-tensor algebra map on its actual completed H⁰, with all inputs supplied. -/
def perfectDelta_completedResidueTensorCartierAlgHom :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI := derivedH0CommRing RES
    letI := derivedH0Algebra RES
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RES).X.obj →ₐ[Q] CQ := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  let k := iteratedTensorCartierCompletedAlgHom R (p : R) d S T
    (perfectDelta_iteratedTensorCartier_isModuleComplete p R S T
      DR DS DT hR hS hT hRS hRT d hd)
  have aux (c : Q) (hc : (q) (p : R) = c) :
      letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra Q c SQ TQ)
      letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra Q c SQ TQ)
      (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
        (boundedAboveCompletedTensorAlgebra Q c SQ TQ).X.obj →ₐ[Q] CQ := by
    subst c
    exact k
  exact aux (p : Q) (map_natCast (q) p)

end SerrePositivity.BhattScholze
