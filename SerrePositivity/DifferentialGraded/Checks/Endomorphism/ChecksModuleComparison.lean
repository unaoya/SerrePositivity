module
public import SerrePositivity.DifferentialGraded.Endomorphism.Module

/-! # 大きい加群dg圏上の比較関手と正則加群の再構成の公理監査 -/
public section
noncomputable section
open CategoryTheory
open SerrePositivity.DifferentialGraded
universe u v
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (E : PerfectDGModuleOver A D S) :
    DGFunctor A (RightModule A (EndomorphismObject E.val)) (RightModule A D) :=
  perfectEndomorphismModuleTensor A D S E

#print axioms endomorphismYonedaApp
#print axioms largeEndomorphismHomBimodule
#print axioms largeEndomorphismHomBimodule_eq
#print axioms endomorphismModuleHom
#print axioms endomorphismModuleAction
#print axioms endomorphismModuleTensor
#print axioms endomorphismModuleHom_self
#print axioms endomorphismModuleTensor_regularIso
#print axioms perfectEndomorphismModuleTensor
