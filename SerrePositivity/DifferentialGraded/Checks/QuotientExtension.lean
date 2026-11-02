module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration
public import Mathlib.Data.ZMod.Basic

/-! # 任意path合成保存・dg延長・制限との往復の受入監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E]

example (S : Set D) (C : ContractedFunctor A D S E) (w v : Word S) (x y z : D) :
    (Cochain.ofHom (appendMap A D w v x y z)).comp
      (pathEvaluation A C (w ++ v) x z) (zero_add 0) =
    (tensorZeroCochain (pathEvaluation A C w x y) (pathEvaluation A C v y z)).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))) (zero_add 0) :=
  pathEvaluation_append A C w v x y z

variable [Small.{u} D]
example (S : Set D) (C : ContractedFunctor A D S E) : DGFunctor A (QuotientObject D S) E :=
  extension A C
example (S : Set D) (C : ContractedFunctor A D S E) :
    restrictContractedFunctor A D S (extension A C) = C := restrict_extension A C

example : restrictContractedFunctor (ZMod 2) PUnit.{1} Set.univ
    (extension (ZMod 2) (canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ)) =
    canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ :=
  restrict_extension (ZMod 2) (canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ)

#print axioms SerrePositivity.DifferentialGraded.tensorZeroCochain_comp
#print axioms SerrePositivity.DifferentialGraded.tensorZeroCochain_assoc
#print axioms SerrePositivity.DifferentialGraded.tensorZeroCochain_id_left
#print axioms SerrePositivity.DifferentialGraded.tensorZeroCochain_id_right
#print axioms SerrePositivity.DifferentialGraded.tensorZeroCochain_postcomp_left
#print axioms SerrePositivity.DifferentialGraded.tensorZeroCochain_postcomp_right
#print axioms SerrePositivity.DifferentialGraded.tensorZeroCochain_precomp
#print axioms SerrePositivity.DifferentialGraded.tensorZeroCochain_multiply_assoc
#print axioms SerrePositivity.DifferentialGraded.tensorCarry_evaluation
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.pathEvaluation_append
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.tensorTwoPathCochain_ext
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalEvaluation_composition
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientEvaluation_composition
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.extension
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.inclusion_comp_extension
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.restrict_extension_homotopy
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.ContractedFunctor.ext
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.restrict_extension
