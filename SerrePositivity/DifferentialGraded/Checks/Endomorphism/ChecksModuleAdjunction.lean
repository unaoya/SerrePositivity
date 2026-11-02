module
public import SerrePositivity.DifferentialGraded.Endomorphism.Module

/-! # 再構成随伴の単位・余単位・三角恒等式の公理監査 -/
public section
noncomputable section
open CategoryTheory
open SerrePositivity.DifferentialGraded
universe u v
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (E : PerfectDGModuleOver A D S) :
    (endomorphismModuleTensor A D E.val).onClosed ⊣ (endomorphismModuleHom A D E.val).onClosed :=
  endomorphismModuleAdjunction A D E.val

#print axioms endomorphismModuleUnit
#print axioms endomorphismModuleCounit
#print axioms endomorphismModule_left_triangle
#print axioms endomorphismModule_right_triangle
#print axioms endomorphismModuleAdjunction
