module
public import SerrePositivity.DifferentialGraded.Quotient.AppendErasure
public import Mathlib.Data.ZMod.Basic

/-! # 全右pathへの連結の消去Leibniz則の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {S : Set D} (w : Word S) (x y z : D) :
    (Cochain.ofHom (appendRight A D w x y z)).comp (erasure A D S x z) (zero_add 1) =
    ((tensorRightHom (internalHom A D S y z) (term A D w x y)
      (internalHom A D S x y)).f 1 (eraseRow A D w x y)).comp
      (Cochain.ofHom (internalComposition A D S x y z)) (add_zero 1) +
    ((tensorLeftHom (term A D w x y) (internalHom A D S y z)
      (internalHom A D S y z)).f 1 (erasure A D S y z)).comp
      (Cochain.ofHom (appendRight A D w x y z)) (add_zero 1) :=
  appendRight_erasure A D w x y z

#print axioms SerrePositivity.DifferentialGraded.prefixTensor_cochain_middle
#print axioms SerrePositivity.DifferentialGraded.prefixTensor_cochain_right
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseMiddle_tensorRight_naturality
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.appendRight_eraseFirst
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.appendLiftCochain
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.appendLiftCochain_add
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.appendLiftCochain_left
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.appendLiftCochain_right
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.appendRight_erasure_cons
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.appendRight_erasure
