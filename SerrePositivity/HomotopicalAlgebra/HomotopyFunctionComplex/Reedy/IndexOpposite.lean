module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Index

/-! # Opposite duality on Reedy latching and matching indices -/

@[expose] public section
universe v u t
noncomputable section
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)

def latchingOpObjEquiv : LatchingIndex r.op (op j) ≃ MatchingIndex r j where
  toFun f := ⟨Under.mk f.obj.hom.unop, f.property.1,
    by
      change ¬MorphismProperty.identities J f.obj.hom.unop
      exact fun h ↦ f.property.2 ((MorphismProperty.identities_op_iff _).2 h)⟩
  invFun f := ⟨Over.mk f.obj.hom.op, f.property.1,
    by
      change ¬MorphismProperty.identities Jᵒᵖ f.obj.hom.op
      intro h
      exact f.property.2 ((MorphismProperty.identities_op_iff _).1 h)⟩
  left_inv f := by
    rcases f with ⟨f, hf⟩
    obtain ⟨x, f, rfl⟩ := Over.mk_surjective f
    rfl
  right_inv f := by
    rcases f with ⟨f, hf⟩
    obtain ⟨x, f, rfl⟩ := Under.mk_surjective f
    rfl

def matchingOpObjEquiv : MatchingIndex r.op (op j) ≃ LatchingIndex r j where
  toFun f := ⟨Over.mk f.obj.hom.unop, f.property.1,
    by
      change ¬MorphismProperty.identities J f.obj.hom.unop
      exact fun h ↦ f.property.2 ((MorphismProperty.identities_op_iff _).2 h)⟩
  invFun f := ⟨Under.mk f.obj.hom.op, f.property.1,
    by
      change ¬MorphismProperty.identities Jᵒᵖ f.obj.hom.op
      intro h
      exact f.property.2 ((MorphismProperty.identities_op_iff _).1 h)⟩
  left_inv f := by
    rcases f with ⟨f, hf⟩
    obtain ⟨x, f, rfl⟩ := Under.mk_surjective f
    rfl
  right_inv f := by
    rcases f with ⟨f, hf⟩
    obtain ⟨x, f, rfl⟩ := Over.mk_surjective f
    rfl

end SerrePositivity.Reedy
