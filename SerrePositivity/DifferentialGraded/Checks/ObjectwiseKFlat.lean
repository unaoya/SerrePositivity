module
public import SerrePositivity.DifferentialGraded.Tensor.ObjectwiseKFlat
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 相対条件とlocal Hom仮定付きobjectwise条件の区別 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (M : ModuleCategory A D) (hM : moduleSemifree A D M) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M) :=
  moduleSemifree_relativeKFlat A D hM

example (hD : localHomKFlat A D) (M : ModuleCategory A D) (hM : moduleSemifree A D M) :
    moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) M) :=
  moduleSemifree_objectwiseKFlat A D hD hM

example (hD : localHomKFlat A D) (x : D) :
    moduleObjectwiseKFlat A D
      (ForgetEnrichment.to (Complex A) (freeSphere A D x (-1))) :=
  freeAt_objectwiseKFlat A D hD x _ (complexSphere_kFlat A (-1))

example : localHomKFlat A PUnit.{1} := fun _ _ => complexKFlat_unit A

example (M : ModuleCategory (ZMod 2) PUnit.{1}) :
    ∃ (P : ModuleCategory (ZMod 2) PUnit.{1}) (q : P ⟶ M),
      moduleSemifree (ZMod 2) PUnit.{1} P ∧
        moduleRelativeKFlat (ZMod 2) PUnit.{1} (ForgetEnrichment.to (Complex (ZMod 2)) P) ∧
        moduleObjectwiseKFlat (ZMod 2) PUnit.{1} (ForgetEnrichment.to (Complex (ZMod 2)) P) ∧
        moduleDegreewiseSurjective (ZMod 2) PUnit.{1} q ∧ moduleQuasiIso (ZMod 2) PUnit.{1} q :=
  exists_objectwiseKFlat_resolution (ZMod 2) PUnit.{1}
    (fun _ _ => complexKFlat_unit (ZMod 2)) M

#print axioms complexKFlat_of_degreewiseSplit
#print axioms localHomKFlat
#print axioms moduleObjectwiseKFlat
#print axioms freeAt_objectwiseKFlat
#print axioms moduleObjectwiseKFlat_colimit
#print axioms moduleObjectwiseKFlat_of_gradedSplit
#print axioms sphereFreePresentation_objectwiseKFlat
#print axioms ModuleSemifreeFiltration.objectwiseKFlat_stage
#print axioms moduleSemifree_objectwiseKFlat
#print axioms exists_objectwiseKFlat_resolution
