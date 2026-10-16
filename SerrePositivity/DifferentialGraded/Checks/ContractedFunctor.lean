module
public import SerrePositivity.DifferentialGraded.Quotient.ContractionCochain
public import Mathlib.Data.ZMod.Basic

/-! # 指定収縮データと商からの制限・ε評価の受入監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E]

example (S : Set D) (G : DGFunctor A (QuotientObject D S) E) : ContractedFunctor A D S E :=
  restrictContractedFunctor A D S G

example (S : Set D) (C : ContractedFunctor A D S E) (b : S) :
    δ 0 1 (contractionCochain A C b) =
    (eraseEpsilon A).comp (Cochain.ofHom (eId (Complex A) (C.toDGFunctor.obj b.val)))
      (add_zero 1) := contractionCochain_differential A C b

example : ContractedFunctor (ZMod 2) PUnit.{1} Set.univ (QuotientObject PUnit.{1} Set.univ) :=
  canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ

#print axioms SerrePositivity.DifferentialGraded.DGFunctor.map_differential_element
#print axioms SerrePositivity.DifferentialGraded.DGFunctor.map_contractingElement
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.ContractedFunctor.postcomp
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.canonicalContractedFunctor
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.restrictContractedFunctor
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.restrictContractedFunctor_homotopy
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.contractionCochain
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.contractionCochain_generator
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.contractionCochain_differential
