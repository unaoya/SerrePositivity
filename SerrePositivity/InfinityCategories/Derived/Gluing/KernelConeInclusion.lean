module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelFunctor
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeRepresentatives

/-! 元の gluing 射の標準円錐への、右包含と同じ閉 kernel comma 射。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y : DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
  (a : ForgetEnrichment.of (Complex R) X ⟶ ForgetEnrichment.of (Complex R) Y)

/-- 比較射の等式による cone の移送は、同じ右包含を保つ。 -/
lemma dgGluingModuleConeInr_eqToIso {P Q : ModuleCategory R C} (f g : P ⟶ Q)
    (h : f = g) :
    moduleConeInr R C f ≫ (eqToIso (congrArg (moduleCone R C) h)).hom =
      moduleConeInr R C g := by
  subst g
  simp

/-- 元の双加群像の円錐から tensor 像への比較は、同じ右包含を回収する。 -/
lemma dgGluingCommaKernelConeIso_inr :
    moduleConeInr R C (dgGluingCommaClosedSourceMap R C D M X Y a) ≫
      (dgGluingCommaKernelConeIso R C D M X Y a).hom =
    (dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.source)).inv ≫
      (Morita.kernelTensor R D C M).onClosed.map
        (moduleConeInr R D ((dgYoneda R D).onClosed.map
          ((dgFunctorCommaSource R D (RightModule R C) M.toFunctor).onClosed.map a))) := by
  rw [dgGluingCommaKernelConeIso, Iso.trans_hom, ← Category.assoc]
  rw [dgGluingModuleConeInr_eqToIso R C _ _
    (dgGluingCommaClosedSourceMap_eq R C D M X Y a), dgGluingKernelConeIso_inr]
  rfl

variable (Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "F" => Morita.kernelTensor R D C M
local notation "KZ" => dgGluingKernelObject R C D M Z
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "lf" => dgGluingConeLeftArrow R C D M Y Z f
local notation "rf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgYoneda R D)) (dgGluingConeRightArrow R C D M Y Z f)

/-- 標準円錐への左右包含の augmentation 正方形は、厳密に可換する。 -/
lemma dgGluingKernelConeInr_square :
    moduleConeInr R C lf ≫ dgGluingConeKernelMorphism R C D M Y Z f =
    dgGluingKernelLift R C D M Z ≫ (F).onClosed.map (moduleConeInr R D rf) := by
  change moduleConeInr R C lf ≫
    (dgGluingConeMorphism R C D M Y Z f ≫ _) = _
  rw [← Category.assoc]
  erw [dgGluingCommaConeMorphism_inr R C D M
    (dgGluingCommaObject R C D M Y) (dgGluingCommaObject R C D M Z)
    ((dgGluingToComma R C D M).onClosed.map f)]
  rw [Category.assoc, dgGluingCommaKernelConeIso_inr]
  simp only [dgGluingKernelLift, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories
