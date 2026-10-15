module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import SerrePositivity.HomologicalAlgebra.CochainAcyclic

/-! # 既存の複体 cone による quasiIso の判定 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A]

/-- 非有界複体の射は、その標準 mapping cone が acyclic であるとき準同型。 -/
lemma complex_quasiIso_iff_acyclic_cone {P Q : Complex A} (f : P ⟶ Q) :
    QuasiIso f ↔ (mappingCone f).Acyclic :=
  SerrePositivity.cochain_quasiIso_iff_cone_acyclic f

end SerrePositivity.DifferentialGraded
