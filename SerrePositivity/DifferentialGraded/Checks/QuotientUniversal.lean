module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration
public import Mathlib.Data.ZMod.Basic

/-! # 指定収縮付きdg商の厳密普遍性・一意性・後合成自然性の受入監査 -/
@[expose] public section
noncomputable section
universe u v w t
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (S : Set D) (E : Type w) [DGCategory A E]

example : DGFunctor A (QuotientObject D S) E ≃ ContractedFunctor A D S E :=
  universalEquiv A D S E
example (G : DGFunctor A (QuotientObject D S) E) :
    extension A (restrictContractedFunctor A D S G) = G := extension_restrict A G
example (C : ContractedFunctor A D S E) :
    restrictContractedFunctor A D S (extension A C) = C := restrict_extension A C
example (C : ContractedFunctor A D S E) :
    ∃! G : DGFunctor A (QuotientObject D S) E, restrictContractedFunctor A D S G = C :=
  existsUnique_extension A C

variable (T : Type t) [DGCategory A T]
example (C : ContractedFunctor A D S E) (H : DGFunctor A E T) :
    extension A (C.postcomp A H) = (extension A C).comp H := extension_postcomp A C H
example (G : DGFunctor A (QuotientObject D S) E) (H : DGFunctor A E T) :
    restrictContractedFunctor A D S (G.comp H) =
      (restrictContractedFunctor A D S G).postcomp A H := restrictContractedFunctor_comp A G H

example : DGFunctor (ZMod 2) (QuotientObject PUnit.{1} Set.univ)
    (QuotientObject PUnit.{1} Set.univ) ≃
    ContractedFunctor (ZMod 2) PUnit.{1} Set.univ (QuotientObject PUnit.{1} Set.univ) :=
  universalEquiv (ZMod 2) PUnit.{1} Set.univ (QuotientObject PUnit.{1} Set.univ)
example : extension (ZMod 2)
    (restrictContractedFunctor (ZMod 2) PUnit.{1} Set.univ
      (extension (ZMod 2) (canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ))) =
    extension (ZMod 2) (canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ) :=
  extension_restrict (ZMod 2) _

#print axioms SerrePositivity.DifferentialGraded.tensorMiddle_left_unit
#print axioms SerrePositivity.DifferentialGraded.tensorSandwich_append
#print axioms SerrePositivity.DifferentialGraded.tensorJoin_right_unit
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.epsilonTerm_append
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prependMap_epsilonTerm_append
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.epsilon_internalComposition_ι
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prefixPath_generated
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.epsilon_generator_span
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.epsilonMiddleCochain_ext₀
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.prefixPath_generator
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.path_inclusion_generator
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.restrictionHomCochain
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.restrictionHomCochain_path
#print axioms
  SerrePositivity.DifferentialGraded.DGQuotient.restrictionHomCochain_eq_internalEvaluation
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.extension_restrict
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.universalEquiv
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.extension_unique
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.existsUnique_extension
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.restrictContractedFunctor_comp
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.extension_postcomp
