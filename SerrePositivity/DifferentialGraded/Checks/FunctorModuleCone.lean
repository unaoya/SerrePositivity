module
public import SerrePositivity.DifferentialGraded.Functor.Closed
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 複体値dg関手の符号規約と標準cone比較射の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGFunctor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (F : DGFunctor A D (Complex A)) {x y z : D}
    (f : GradedHom A x y (-1)) (g : GradedHom A y z 1) :
    (F.map x z).f 0 (compose A g f (by decide)) =
      ((F.map x y).f (-1) f).comp ((F.map y z).f 1 g) (by decide) :=
  map_compose_cochain A F f g (by decide)

example (F : DGFunctor A (RightModule A D) (Complex A))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone.inr ((F.toComplexFunctor A).map f) ≫ moduleConeImageComparison A D F f =
      (F.toComplexFunctor A).map (moduleConeInr A D f) :=
  moduleConeImageComparison_inr A D F f

example {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    moduleConeImageInl A D (moduleEvaluationDG A D x) f =
      mappingCone.inl ((moduleEvaluation A D x).map f) :=
  moduleConeInlElement_π A D f x

example {M N : ModuleCategory (ZMod 2) PUnit.{1}} (f : M ⟶ N) (x : PUnit.{1}) :
    moduleConeImageInl (ZMod 2) PUnit.{1} (moduleEvaluationDG (ZMod 2) PUnit.{1} x) f =
      mappingCone.inl ((moduleEvaluation (ZMod 2) PUnit.{1} x).map f) :=
  moduleConeInlElement_π (ZMod 2) PUnit.{1} f x

#print axioms toComplexFunctor
#print axioms map_closedElement
#print axioms map_d_cochain
#print axioms map_compose_cochain
#print axioms moduleConeImageInl
#print axioms moduleConeImageInl_d
#print axioms moduleConeImageComparison
#print axioms moduleConeImageComparison_inr
#print axioms moduleConeImageComparison_inl
