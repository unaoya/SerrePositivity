module
public import SerrePositivity.DifferentialGraded.Quotient.Path.Evaluation
public import Mathlib.Data.ZMod.Basic

/-! # 有限・全path評価の先頭Hom作用との整合性の受入監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E]

example (S : Set D) (C : ContractedFunctor A D S E) (w : Word S) (x y z : D) :
    (Cochain.ofHom (prependMap A D w x y z)).comp (pathEvaluation A C w x z) (zero_add 0) =
    (tensorZeroCochain (Cochain.ofHom (C.toDGFunctor.map x y)) (pathEvaluation A C w y z)).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))) (zero_add 0) :=
  pathEvaluation_prepend A C w x y z

example (b : (Set.univ : Set PUnit.{1})) :
    (Cochain.ofHom (prependMap (ZMod 2) PUnit.{1} [b] PUnit.unit PUnit.unit PUnit.unit)).comp
      (pathEvaluation (ZMod 2) (canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ)
        [b] PUnit.unit PUnit.unit) (zero_add 0) =
    (tensorZeroCochain
      (Cochain.ofHom ((canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ).toDGFunctor.map
        PUnit.unit PUnit.unit))
      (pathEvaluation (ZMod 2) (canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ)
        [b] PUnit.unit PUnit.unit)).comp
      (Cochain.ofHom (eComp (Complex (ZMod 2))
        (⟨PUnit.unit⟩ : QuotientObject PUnit.{1} Set.univ) ⟨PUnit.unit⟩ ⟨PUnit.unit⟩)) (zero_add 0) :=
  pathEvaluation_prepend (ZMod 2) (canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ)
    [b] PUnit.unit PUnit.unit PUnit.unit

#print axioms SerrePositivity.DifferentialGraded.rightTripleCochain_ext
#print axioms SerrePositivity.DifferentialGraded.rightTripleCochain_ext₀
#print axioms SerrePositivity.DifferentialGraded.tensorJoin_evaluation
#print axioms SerrePositivity.DifferentialGraded.tensorZeroCochain_precomp_right
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.pathEvaluation_prepend
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalEvaluation_prepend
