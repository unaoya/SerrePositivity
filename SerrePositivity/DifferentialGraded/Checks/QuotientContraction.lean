module
public import SerrePositivity.DifferentialGraded.Quotient.Path.Evaluation
public import Mathlib.Data.ZMod.Basic

/-! # 指定εの次数−1と最終微分dε=idの受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (b : S) :
    (quotientHom A D S b.val b.val).d (-1) 0 (epsilonElement A D S b) =
      (unitElement A (⟨b.val⟩ : QuotientObject D S)).val := differential_epsilonElement A D S b

example (b : (Set.univ : Set PUnit.{1})) :
    (quotientHom (ZMod 2) PUnit.{1} Set.univ b.val b.val).d (-1) 0
      (epsilonElement (ZMod 2) PUnit.{1} Set.univ b) =
    (unitElement (ZMod 2) (⟨b.val⟩ : QuotientObject PUnit.{1} Set.univ)).val :=
  differential_epsilonElement (ZMod 2) PUnit.{1} Set.univ b

#print axioms SerrePositivity.DifferentialGraded.unitSandwich_apply
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.epsilonTerm_generator
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.epsilonElement
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseFirst_epsilonTerm
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.erasure_epsilonElement
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internal_d_epsilonElement
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.differential_epsilonElement
