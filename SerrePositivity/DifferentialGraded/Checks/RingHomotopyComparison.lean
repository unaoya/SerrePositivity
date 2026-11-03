module
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # 全Hom同型によるH⁰の完全忠実性と一対象環比較の監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example (D : Type v) (E : Type w) [DGCategory A D] [DGCategory A E]
    (F : DGFunctor A D E) (h : ∀ x y, IsIso (F.map x y)) : F.onHomotopy.Full :=
  F.onHomotopy_full_of_homIso h
example (D : Type v) (E : Type w) [DGCategory A D] [DGCategory A E]
    (F : DGFunctor A D E) (h : ∀ x y, IsIso (F.map x y)) : F.onHomotopy.Faithful :=
  F.onHomotopy_faithful_of_homIso h
example : (ringConstantDG A).onHomotopy.IsEquivalence := inferInstance
example : (moduleEvaluationDG A PUnit.{1} PUnit.unit).onHomotopy.IsEquivalence := inferInstance
example : (ringConstantDG A).onHomotopy.Linear A := inferInstance
example : (ringConstantDG (ZMod 2)).onHomotopy.IsEquivalence := inferInstance

#print axioms DGFunctor.onClosed_full_of_homIso
#print axioms DGFunctor.onClosed_faithful_of_homIso
#print axioms DGFunctor.boundary_iff_of_homIso
#print axioms DGFunctor.onHomotopy_full_of_homIso
#print axioms DGFunctor.onHomotopy_faithful_of_homIso
#print axioms ringConstantDGHomotopyFull
#print axioms ringConstantDGHomotopyFaithful
#print axioms ringConstantDGHomotopyIsEquivalence
#print axioms ringConstantHomotopyEquivalence
#print axioms ringEvaluationDGHomotopyFull
#print axioms ringEvaluationDGHomotopyFaithful
#print axioms ringEvaluationDGHomotopyIsEquivalence
#print axioms ringEvaluationHomotopyEquivalence
