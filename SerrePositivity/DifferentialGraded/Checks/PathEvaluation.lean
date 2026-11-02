module
public import SerrePositivity.DifferentialGraded.Quotient.Path.Evaluation
public import Mathlib.Data.ZMod.Basic

/-! # 有限path評価と全直和へのcochain貼合せの受入監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E]

example (S : Set D) (C : ContractedFunctor A D S E) (b : S) :
    (pathEvaluation A C [b] b.val b.val).v (-1) (-1) (add_zero (-1))
      ((epsilonTerm A D b).f (-1)
        ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))) = C.homotopy b :=
  pathEvaluation_epsilonTerm A C b

variable [Small.{u} D]
example (S : Set D) (C : ContractedFunctor A D S E) (x y : D) :
    (Cochain.ofHom (originalHom A D S x y)).comp (internalEvaluation A C x y) (zero_add 0) =
      Cochain.ofHom (C.toDGFunctor.map x y) := internalEvaluation_original A C x y

example (b : (Set.univ : Set PUnit.{1})) :
    (Cochain.ofHom (epsilon (ZMod 2) PUnit.{1} Set.univ b)).comp
      (internalEvaluation (ZMod 2) (canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ)
        b.val b.val) (zero_add 0) =
    contractionCochain (ZMod 2) (canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ) b :=
  internalEvaluation_epsilon (ZMod 2) (canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ) b

#print axioms SerrePositivity.DifferentialGraded.homComplexMap_differential
#print axioms SerrePositivity.DifferentialGraded.tensorZeroCochain
#print axioms SerrePositivity.DifferentialGraded.tensorZeroCochain_ofHom
#print axioms SerrePositivity.DifferentialGraded.tensorZeroCochain_apply
#print axioms SerrePositivity.DifferentialGraded.tensorZeroCochain_differential
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.pathEvaluation
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.pathEvaluation_nil
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.pathEvaluation_cons_generator
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.pathEvaluation_epsilonTerm
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.pathCochainDesc
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.pathCochainDesc_precomp
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.pathCochainDesc_unique
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalEvaluation
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalEvaluation_precomp
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalEvaluation_original
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalEvaluation_epsilon
