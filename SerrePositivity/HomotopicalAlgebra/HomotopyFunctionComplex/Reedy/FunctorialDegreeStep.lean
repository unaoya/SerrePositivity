module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorialExtension
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorFactorizationFamily
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.DegreeFactorizationStep
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryDegree

/-! # Functorial factorization on the next closed degree restriction

The ordinary-degree comparisons are natural in the original input arrow.
Conjugating the functorial attaching-diagram factorization by these
comparisons gives a factorization in the original arrow functor category.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy.FunctorDegreeStep
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J) (hinj : Function.Injective r.deg)
  {C : Type u'} [Category.{v'} C]
  [HasColimitsOfShape (LatchingIndex r j) C] [HasLimitsOfShape (MatchingIndex r j) C]
  [HasPushouts C] [HasPullbacks C]
  {left right : MorphismProperty C} (data : MorphismProperty.FunctorialFactorizationData left right)
  (a : FunctorFactorAt (C := C) r (r.deg j))

abbrev upperRestrictionFunctor : (J ⥤ C) ⥤ (Upper r (r.deg j) ⥤ C) :=
  (Functor.whiskeringLeft _ _ C).obj (upperInclusion r (r.deg j))

abbrev middle : Arrow (J ⥤ C) ⥤ (Upper r (r.deg j) ⥤ C) :=
  a.problemFunctor r j ⋙ FactorizationProblem.extensionFunctor r j C data ⋙
    BoundaryDiagram.degreeFunctor r j C hinj

abbrev sourceIso : a.problemFunctor r j ⋙ FactorizationProblem.sourceFunctor r j C ⋙
      BoundaryDiagram.degreeFunctor r j C hinj ≅
    Arrow.leftFunc ⋙ upperRestrictionFunctor (C := C) r j :=
  NatIso.ofComponents
    (fun φ ↦ BoundaryExtension.degreeOfFunctorIso r j φ.left hinj)
    (fun s ↦ BoundaryExtension.degreeOfFunctorIso_naturality r j _ hinj s.left)

abbrev targetIso : a.problemFunctor r j ⋙ FactorizationProblem.targetFunctor r j C ⋙
      BoundaryDiagram.degreeFunctor r j C hinj ≅
    Arrow.rightFunc ⋙ upperRestrictionFunctor (C := C) r j :=
  NatIso.ofComponents
    (fun φ ↦ BoundaryExtension.degreeOfFunctorIso r j φ.right hinj)
    (fun s ↦ BoundaryExtension.degreeOfFunctorIso_naturality r j _ hinj s.right)

abbrev leftTransformation : Arrow.leftFunc ⋙ upperRestrictionFunctor (C := C) r j ⟶
    middle r j hinj data a :=
  (sourceIso r j hinj a).inv ≫ Functor.whiskerLeft (a.problemFunctor r j)
    (Functor.whiskerRight (FactorizationProblem.leftTransformation r j C data)
      (BoundaryDiagram.degreeFunctor r j C hinj))

abbrev rightTransformation : middle r j hinj data a ⟶
    Arrow.rightFunc ⋙ upperRestrictionFunctor (C := C) r j :=
  Functor.whiskerLeft (a.problemFunctor r j)
    (Functor.whiskerRight (FactorizationProblem.rightTransformation r j C data)
      (BoundaryDiagram.degreeFunctor r j C hinj)) ≫ (targetIso r j hinj a).hom

abbrev factor : MorphismProperty.MapFactorizationData ⊤ ⊤
    (Functor.whiskerRight Arrow.leftToRight (upperRestrictionFunctor (C := C) r j)) where
  Z := middle r j hinj data a
  i := leftTransformation r j hinj data a
  p := rightTransformation r j hinj data a
  fac := by
    apply NatTrans.ext
    funext φ
    exact DegreeFactorizationStep.leftMap_rightMap r j hinj φ.hom (a.atArrow φ)
      (data.factorizationData (RelativeExtension.map
        (BoundaryExtension.mapOfNatTrans r j φ.hom) (a.atArrow φ)))
  hi := trivial
  hp := trivial

end SerrePositivity.Reedy.FunctorDegreeStep
