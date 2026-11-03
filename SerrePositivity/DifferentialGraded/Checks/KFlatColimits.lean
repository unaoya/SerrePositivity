module
public import SerrePositivity.DifferentialGraded.Tensor.Enriched

public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # K-flat性の余積・逐次余極限保存と独立宇宙の検査 -/
@[expose] public section
noncomputable section
universe u v w w'
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {J : Type w} [Category.{w'} J] [Small.{u} J]
    [HasExactColimitsOfShape J (ModuleCat.{u} A)] (F : J ⥤ ModuleCategory A D)
    (h : ∀ j, moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (F.obj j))) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (colimit F)) :=
  moduleRelativeKFlat_colimit A D F h

example (M : ℕ ⥤ ModuleCategory A D)
    (h : ∀ n, moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (M.obj n))) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (colimit M)) :=
  moduleRelativeKFlat_sequentialColimit A D M h

example (x : Fin 3 → D) : moduleRelativeKFlat A D
    (ForgetEnrichment.to (Complex A)
      (∐ fun i => ForgetEnrichment.of (Complex A) (representable A (x i)))) := by
  have : AB4OfSize.{0} (ModuleCat.{u} A) := AB4OfSize_shrink (ModuleCat.{u} A)
  exact moduleRelativeKFlat_colimit A D
    (Discrete.functor fun i => ForgetEnrichment.of (Complex A) (representable A (x i)))
    (fun i => representable_relativeKFlat A D (x i.as))

example : complexKFlat A (colimit ((Functor.const ℕ).obj (𝟙_ (Complex A)))) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  exact complexKFlat_colimit A _ (fun _ => complexKFlat_unit A)

example (x : PUnit.{1}) : moduleRelativeKFlat (ZMod 2) PUnit.{1}
    (ForgetEnrichment.to (Complex (ZMod 2))
      (colimit ((Functor.const ℕ).obj
        (ForgetEnrichment.of (Complex (ZMod 2)) (representable (ZMod 2) x))))) :=
  moduleRelativeKFlat_sequentialColimit (ZMod 2) PUnit.{1} _
    (fun _ => representable_relativeKFlat (ZMod 2) PUnit.{1} x)

#print axioms complexDiagramTranspose
#print axioms complexDiagramTranspose_acyclic
#print axioms complex_colimit_acyclic
#print axioms complexKFlat_colimit
#print axioms moduleRelativeKFlat_colimit
#print axioms moduleRelativeKFlat_coproduct
#print axioms moduleRelativeKFlat_sequentialColimit
