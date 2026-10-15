module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryReconstruction
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionDegree

/-! # Recovering attaching diagrams after extension to the closed degree

The comparison is a natural isomorphism of functors on attaching diagrams,
so it supplies comparisons for arrows, rather than only for isolated objects.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy.BoundaryDiagram
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J) (C : Type u') [Category.{v'} C]

abbrev adjoinToUpper : Adjoin r j ⥤ Upper r (r.deg j) :=
  (upperProperty r (r.deg j)).lift (adjoinInclusion r j) (adjoinObj_degree_le r j)

lemma adjoinDegreeObj (x : Adjoin r j) :
    degreeIndexObj r j ((adjoinToUpper r j).obj x) = x := by
  cases x with
  | none =>
    change (if h : r.deg j < r.deg j then some (⟨j, h⟩ : Lower r (r.deg j)) else none) = none
    simp only [lt_self_iff_false, dite_false]
  | some x =>
    change (if h : r.deg x.obj < r.deg j then some ⟨x.obj, h⟩ else none) = some x
    simp only [dite_eq_left x.property]

def adjoinDegreeIso (hinj : Function.Injective r.deg) :
    adjoinToUpper r j ⋙ degreeIndex r j hinj ≅ 𝟭 (Adjoin r j) :=
  NatIso.ofComponents (fun x ↦ eqToIso (adjoinDegreeObj r j x)) (fun {x y} f ↦ by
    apply InducedCategory.hom_ext
    change (eqToHom (degreeIndexObj_eq r j hinj ((adjoinToUpper r j).obj x)) ≫
        f.hom ≫ eqToHom (degreeIndexObj_eq r j hinj ((adjoinToUpper r j).obj y)).symm) ≫
        (eqToHom (adjoinDegreeObj r j y)).hom =
      (eqToHom (adjoinDegreeObj r j x)).hom ≫ f.hom
    simp only [InducedCategory.eqToHom_hom]
    exact conjugate_eqToHom _ _ _)

abbrev degreeFunctor (hinj : Function.Injective r.deg) :
    BoundaryDiagram r j C ⥤ (Upper r (r.deg j) ⥤ C) :=
  toAdjoinFunctor r j C ⋙ (Functor.whiskeringLeft _ _ C).obj (degreeIndex r j hinj)

abbrev fromUpperFunctor : (Upper r (r.deg j) ⥤ C) ⥤ BoundaryDiagram r j C :=
  (Functor.whiskeringLeft _ _ C).obj (adjoinToUpper r j) ⋙ fromAdjoinFunctor r j C

abbrev degreePrecompositionIso (hinj : Function.Injective r.deg) :
    (Functor.whiskeringLeft _ _ C).obj (degreeIndex r j hinj) ⋙
        (Functor.whiskeringLeft _ _ C).obj (adjoinToUpper r j) ≅ 𝟭 (Adjoin r j ⥤ C) :=
  (Functor.whiskeringLeft _ _ C).mapIso (adjoinDegreeIso r j hinj) ≪≫
    Functor.whiskeringLeftObjIdIso

def degreeReconstructionIso (hinj : Function.Injective r.deg) :
    degreeFunctor r j C hinj ⋙ fromUpperFunctor r j C ≅ 𝟭 (BoundaryDiagram r j C) :=
  Functor.isoWhiskerLeft (toAdjoinFunctor r j C)
      (Functor.isoWhiskerRight (degreePrecompositionIso r j C hinj) (fromAdjoinFunctor r j C)) ≪≫
    reconstructionIso r j C

@[simp]
lemma fromUpperFunctor_obj_original (F : J ⥤ C) :
    (fromUpperFunctor r j C).obj (upperInclusion r (r.deg j) ⋙ F) =
      (fromFunctor r j C).obj F := rfl

@[simp]
lemma fromUpperFunctor_map_original {F G : J ⥤ C} (τ : F ⟶ G) :
    (fromUpperFunctor r j C).map (Functor.whiskerLeft (upperInclusion r (r.deg j)) τ) =
      (fromFunctor r j C).map τ := rfl

end SerrePositivity.Reedy.BoundaryDiagram
