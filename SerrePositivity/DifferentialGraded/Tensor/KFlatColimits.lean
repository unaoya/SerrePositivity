module
public import SerrePositivity.DifferentialGraded.Tensor.KFlat
public import SerrePositivity.DifferentialGraded.Tensor.HomAdjunctionLaws
public import SerrePositivity.DifferentialGraded.Module.Colimits
public import SerrePositivity.DifferentialGraded.Complexes.ExactColimits
public import Mathlib.Algebra.Category.ModuleCat.AB

/-! # 相対K-flat加群のexactな余極限 -/
@[expose] public section
noncomputable section
universe u v w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [DGCategory A D] [Small.{u} D] in
/-- A上のK-flat複体はModuleCatのexactな余極限で閉じる。 -/
lemma complexKFlat_colimit {J : Type w} [Category.{w'} J] [Small.{u} J]
    [HasExactColimitsOfShape J (ModuleCat.{u} A)] (F : J ⥤ Complex A)
    (h : ∀ j, complexKFlat A (F.obj j)) : complexKFlat A (colimit F) := by
  intro L hL
  have hc := complex_colimit_acyclic A (F ⋙ tensorRight L) (fun j => h j L hL)
  intro n
  exact (hc n).of_iso (preservesColimitIso (tensorRight L) F).symm

/-- ModuleCatのexactな余極限の形に沿う相対K-flat加群の余極限は相対K-flat。 -/
lemma moduleRelativeKFlat_colimit {J : Type w} [Category.{w'} J] [Small.{u} J]
    [HasExactColimitsOfShape J (ModuleCat.{u} A)]
    (F : J ⥤ ModuleCategory A D)
    (h : ∀ j, moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (F.obj j))) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (colimit F)) := by
  intro N hN
  have hc := complex_colimit_acyclic A (F ⋙ BalancedTensor.rightTensorFunctor A D N)
    (fun j => h j N hN)
  intro n
  exact (hc n).of_iso (preservesColimitIso (BalancedTensor.rightTensorFunctor A D N) F).symm

/-- u-smallな族の余積は相対K-flat性を保つ。 -/
lemma moduleRelativeKFlat_coproduct {I : Type u} (M : I → RightModule A D)
    (h : ∀ i, moduleRelativeKFlat A D (M i)) :
    moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) (∐ fun i => ForgetEnrichment.of (Complex A) (M i))) :=
  moduleRelativeKFlat_colimit A D (Discrete.functor fun i => ForgetEnrichment.of (Complex A) (M i))
    (fun i => h i.as)

/-- 非有界加群の逐次余極限は相対K-flat性を保つ。 -/
lemma moduleRelativeKFlat_sequentialColimit (F : ℕ ⥤ ModuleCategory A D)
    (h : ∀ j, moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (F.obj j))) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (colimit F)) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  exact moduleRelativeKFlat_colimit A D F h

end SerrePositivity.DifferentialGraded
