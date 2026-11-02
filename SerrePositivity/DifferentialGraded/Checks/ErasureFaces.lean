module
public import SerrePositivity.DifferentialGraded.Quotient.Erasure
public import Mathlib.Data.ZMod.Basic

/-! # ε消去・任意位置のface・有限消去和の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

example {S : Set D} (w : Word S) (i : ℕ) (x y : D) :
    Cochain (term A D w x y) (term A D (w.eraseIdx i) x y) 1 :=
  eraseFace A D w i x y
example {S : Set D} (w : Word S) (i : ℕ) (x y : D) :
    δ 1 2 (eraseFace A D w i x y) = 0 := eraseFace_closed A D w i x y
example [Small.{u} D] {S : Set D} (w : Word S) (x y : D) :
    δ 1 2 (eraseRow A D w x y) = 0 := eraseRow_closed A D w x y
example (P Q : Complex A) : δ 1 2 (eraseMiddle A P Q) = 0 := eraseMiddle_closed A P Q
example (b : (Set.univ : Set PUnit.{1})) :
    δ 1 2 (eraseRow (ZMod 2) PUnit.{1} [b, b] PUnit.unit PUnit.unit) = 0 :=
  eraseRow_closed (ZMod 2) PUnit.{1} [b, b] PUnit.unit PUnit.unit

#print axioms homComplexMap_closed
#print axioms cochain_v_units_smul
#print axioms tensorRightHom
#print axioms tensorRightHom_cochain
#print axioms tensorRightHom_apply
#print axioms DGQuotient.eraseEpsilon
#print axioms DGQuotient.eraseEpsilon_closed
#print axioms DGQuotient.eraseEpsilon_v
#print axioms DGQuotient.eraseEpsilon_generator
#print axioms DGQuotient.eraseLeftTensor
#print axioms DGQuotient.eraseLeftTensor_closed
#print axioms DGQuotient.eraseRightTensor
#print axioms DGQuotient.eraseRightTensor_closed
#print axioms DGQuotient.eraseLeftTensor_apply
#print axioms DGQuotient.eraseRightTensor_apply
#print axioms DGQuotient.eraseMiddle
#print axioms DGQuotient.eraseMiddle_closed
#print axioms DGQuotient.eraseFirst
#print axioms DGQuotient.eraseFirst_closed
#print axioms DGQuotient.eraseFace
#print axioms DGQuotient.eraseFace_nil
#print axioms DGQuotient.eraseFace_zero
#print axioms DGQuotient.eraseFace_closed
#print axioms DGQuotient.eraseSummand
#print axioms DGQuotient.eraseSummand_closed
#print axioms DGQuotient.eraseRow
#print axioms DGQuotient.eraseRow_closed
#print axioms DGQuotient.eraseRow_nil
#print axioms DGQuotient.eraseRow_singleton
