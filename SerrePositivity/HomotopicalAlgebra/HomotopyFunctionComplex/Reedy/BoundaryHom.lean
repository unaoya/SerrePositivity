module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.IndexOppositeEquivalence
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Objects
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Contravariant boundary Hom sends latching colimits to matching limits

The result is for any contravariant functor preserving the particular
opposite latching limit. Its comparison formula identifies the actual
matching map, rather than only its source and target objects.
-/

@[expose] public section
universe v u t vV uV vW uW
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite

namespace SerrePositivity.Reedy.BoundaryHom
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)
  {V : Type uV} [Category.{vV} V] {W : Type uW} [Category.{vW} W]
  (A : J ⥤ V) (H : Vᵒᵖ ⥤ W)
  [HasColimitsOfShape (LatchingIndex r j) V]

/-- The canonical cone obtained from the opposite of the actual latching cocone. -/
abbrev cone : Cone (matchingTarget r.op (op j) ⋙ A.op ⋙ H) :=
  (H.mapCone (colimit.cocone (latchingSource r j ⋙ A)).op).whisker (matchingOpFunctor r j)

variable [PreservesLimit (latchingSource r j ⋙ A).op H]

/-- The limit property follows from duality, preservation, and the actual index equivalence. -/
def isLimit : IsLimit (cone r j A H) :=
  (isLimitOfPreserves H (colimit.isColimit (latchingSource r j ⋙ A)).op).whiskerEquivalence
    (matchingOpEquivalence r j)

variable [HasLimitsOfShape (MatchingIndex r.op (op j)) W]

/-- The concrete boundary-Hom object is the actual matching object. -/
def iso : H.obj (op ((latchingEvaluation r j).obj A)) ≅
    (matchingEvaluation r.op (op j)).obj (A.op ⋙ H) :=
  (isLimit r j A H).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
lemma iso_hom_π (f : MatchingIndex r.op (op j)) :
    (iso r j A H).hom ≫ limit.π (matchingTarget r.op (op j) ⋙ A.op ⋙ H) f =
      H.map (colimit.ι (latchingSource r j ⋙ A) (matchingOpObjEquiv r j f)).op :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ f

/-- The actual matching comparison is contravariant application of the latching comparison. -/
@[reassoc]
lemma comparison :
    H.map ((latchingComparison r j).app A).op ≫ (iso r j A H).hom =
      (matchingComparison r.op (op j)).app (A.op ⋙ H) := by
  apply limit.hom_ext
  intro f
  rw [Category.assoc]
  refine (congrArg (fun k => H.map ((latchingComparison r j).app A).op ≫ k)
    (iso_hom_π r j A H f)).trans ?_
  refine Eq.trans ?_ (limit.lift_π (matchingCone r.op (A.op ⋙ H) (op j)) f).symm
  change H.map ((latchingComparison r j).app A).op ≫
      H.map (colimit.ι (latchingSource r j ⋙ A) (matchingOpObjEquiv r j f)).op =
    H.map (A.map f.obj.hom.unop).op
  rw [← H.map_comp, ← op_comp]
  exact congrArg H.map (congrArg Quiver.Hom.op
    (colimit.ι_desc (latchingCocone r A j) (matchingOpObjEquiv r j f)))

/-- The boundary comparison is natural in a transformation of contravariant functors. -/
@[reassoc]
lemma iso_naturality {H' : Vᵒᵖ ⥤ W}
    [PreservesLimit (latchingSource r j ⋙ A).op H'] (τ : H ⟶ H') :
    (iso r j A H).hom ≫ (matchingEvaluation r.op (op j)).map (Functor.whiskerLeft A.op τ) =
      τ.app (op ((latchingEvaluation r j).obj A)) ≫ (iso r j A H').hom := by
  apply limit.hom_ext
  intro f
  let t := Functor.whiskerLeft (matchingTarget r.op (op j)) (Functor.whiskerLeft A.op τ)
  change ((iso r j A H).hom ≫ lim.map t) ≫
      limit.π (matchingTarget r.op (op j) ⋙ A.op ⋙ H') f = _
  rw [Category.assoc, limit.map_π]
  change (iso r j A H).hom ≫
      (limit.π (matchingTarget r.op (op j) ⋙ A.op ⋙ H) f ≫
        τ.app (op (A.obj f.obj.right.unop))) = _
  rw [← Category.assoc]
  refine (congrArg (fun k => k ≫ τ.app (op (A.obj f.obj.right.unop)))
    (iso_hom_π r j A H f)).trans ?_
  have he := τ.naturality
    (colimit.ι (latchingSource r j ⋙ A) (matchingOpObjEquiv r j f)).op
  exact he.trans ((congrArg (fun k => τ.app (op ((latchingEvaluation r j).obj A)) ≫ k)
    (iso_hom_π r j A H' f).symm).trans (Category.assoc _ _ _).symm)

end SerrePositivity.Reedy.BoundaryHom
