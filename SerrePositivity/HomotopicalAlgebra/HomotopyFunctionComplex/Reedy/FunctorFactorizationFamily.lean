module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationProblem

/-! # Families of lower-degree factorizations over the original arrow category

A factorization in a functor category packages the middle functor and the
two natural factor maps. Evaluating this family gives a one-step problem;
its naturality supplies the actual problem morphisms on every square.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) {C : Type u'} [Category.{v'} C]

abbrev restrictionFunctor (a : α) : (J ⥤ C) ⥤ (Lower r a ⥤ C) :=
  (Functor.whiskeringLeft _ _ C).obj (lowerInclusion r a)

abbrev restrictedArrowTransformation (a : α) :
    Arrow.leftFunc ⋙ restrictionFunctor (C := C) r a ⟶ Arrow.rightFunc ⋙ restrictionFunctor r a :=
  Functor.whiskerRight Arrow.leftToRight (restrictionFunctor r a)

abbrev FunctorFactorAt (a : α) := MorphismProperty.MapFactorizationData ⊤ ⊤
  (restrictedArrowTransformation (C := C) r a)

namespace FunctorFactorAt
variable {r} {a : α} (d : FunctorFactorAt (C := C) r a)

abbrev atArrow (φ : Arrow (J ⥤ C)) : MorphismProperty.MapFactorizationData ⊤ ⊤
    (Functor.whiskerLeft (lowerInclusion r a) φ.hom) where
  Z := d.Z.obj φ
  i := d.i.app φ
  p := d.p.app φ
  fac := congr_app d.fac φ
  hi := trivial
  hp := trivial

variable (r) in
abbrev ofSourceData (a : α) {left right : MorphismProperty C}
    (data : MorphismProperty.FunctorialFactorizationData left right) :
    FunctorFactorAt (C := C) r a where
  Z := (restrictionFunctor r a).mapArrow ⋙ (data.functorCategory (Lower r a)).Z
  i := Functor.whiskerLeft (restrictionFunctor r a).mapArrow
    (data.functorCategory (Lower r a)).i
  p := Functor.whiskerLeft (restrictionFunctor r a).mapArrow
    (data.functorCategory (Lower r a)).p
  fac := by
    apply NatTrans.ext
    funext φ
    exact (data.functorCategory (Lower r a)).fac_app
  hi := trivial
  hp := trivial

variable (r) (j : J) (d : FunctorFactorAt (C := C) r (r.deg j)) in
abbrev problemFunctor : Arrow (J ⥤ C) ⥤ FactorizationProblem r j C where
  obj φ :=
    { source := Arrow.mk ((BoundaryDiagram.fromFunctor r j C).map φ.hom)
      factor := atArrow d φ }
  map s :=
    { boundary := (BoundaryDiagram.fromFunctor r j C).mapArrow.map s
      middle := d.Z.map s
      left := d.i.naturality s
      right := d.p.naturality s }
  map_id φ := by
    apply FactorizationProblem.Hom.ext
    · exact (BoundaryDiagram.fromFunctor r j C).mapArrow.map_id φ
    · exact d.Z.map_id φ
  map_comp s t := by
    apply FactorizationProblem.Hom.ext
    · exact (BoundaryDiagram.fromFunctor r j C).mapArrow.map_comp s t
    · exact d.Z.map_comp s t

end FunctorFactorAt
end SerrePositivity.Reedy
