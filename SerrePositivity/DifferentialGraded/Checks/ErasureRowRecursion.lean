module
public import SerrePositivity.DifferentialGraded.Quotient.Append
public import Mathlib.Data.ZMod.Basic

/-! # 非空pathの消去和再帰と全作用素の前方因子分解の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {S : Set D} (b : S) (w : Word S) (x y : D) :
    eraseRow A D (b :: w) x y =
    (eraseFirst A D b w x y).comp (Cochain.ofHom (ι A D S x y w)) (add_zero 1) +
      prefixTailCochain A D b w x y 1 (eraseRow A D w b.val y) := eraseRow_cons A D b w x y
example (b : (Set.univ : Set PUnit.{1})) :
    homObject (ZMod 2) PUnit.{1} PUnit.unit PUnit.unit ⊗
      (epsilonComplex (ZMod 2) ⊗ internalHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit) ⟶
        internalHom (ZMod 2) PUnit.{1} Set.univ PUnit.unit PUnit.unit :=
  prefixPath (ZMod 2) PUnit.{1} b PUnit.unit PUnit.unit

#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prefixPathCofanIsColimit
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prefixPath
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prefixPath_ι
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prefixPathCochain_ext
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prefixTailCochain
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseSummand_cons_succ
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseRow_cons
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseHead_naturality
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseMiddle_naturality
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prefixPath_erasure
