module
public import SerrePositivity.DifferentialGraded.Quotient.PrependErasure
public import Mathlib.Data.ZMod.Basic

/-! # 全位置の先頭Hom自然性・全消去作用素との可換性の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (x y z : D) :
    (Cochain.ofHom (internalPrepend A D S x y z)).comp (erasure A D S x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (internalHom A D S y z)
      (internalHom A D S y z)).f 1 (erasure A D S y z)).comp
      (Cochain.ofHom (internalPrepend A D S x y z)) (add_zero 1) :=
  internalPrepend_erasure A D S x y z
example : homObject (ZMod 2) PUnit.{1} PUnit.unit PUnit.unit ⊗
    internalHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit ⟶
      internalHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit :=
  internalPrepend (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit PUnit.unit

#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prependMap_eraseFace
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalPrepend
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalPrepend_ι
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prependMap_eraseSummand
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prependMap_eraseRow
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.tensorLeftPathCochain_ext
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalPrepend_erasure
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalPrepend_erasure_apply
