module
public import SerrePositivity.DifferentialGraded.Module.AcyclicTriangulated

/-! # acyclic部分圏と指定準同型のVerdierクラスの受入検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example : (moduleHomotopyAcyclic A D).IsTriangulated := inferInstance
example : (moduleHomotopyAcyclic A D).trW = moduleHomotopyQuasiIso A D :=
  moduleHomotopyAcyclic_trW_eq A D
#print axioms moduleHomotopyAcyclicClosedUnderIso
#print axioms moduleHomotopyAcyclicContainsZero
#print axioms moduleHomotopyAcyclicStableShift
#print axioms moduleHomotopyAcyclicTriangulatedClosed₂
#print axioms moduleHomotopyAcyclicIsTriangulated
#print axioms moduleHomotopyAcyclic_trW_eq
