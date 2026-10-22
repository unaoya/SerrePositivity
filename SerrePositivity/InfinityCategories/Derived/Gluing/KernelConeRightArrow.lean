module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeInclusion
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaStrictLift

/-! 標準加群円錐への、第三 cochain 零の実閉 kernel comma 包含。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "F" => Morita.kernelTensor R D C M
local notation "KZ" => dgGluingKernelObject R C D M Z
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "lf" => dgGluingConeLeftArrow R C D M Y Z f
local notation "rf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgYoneda R D)) (dgGluingConeRightArrow R C D M Y Z f)

/-- 同じ二つの加群円錐の右包含からなる、標準 kernel 円錐への閉射。 -/
def dgGluingKernelConeInr : ForgetEnrichment.of (Complex R) KZ ⟶
    ForgetEnrichment.of (Complex R) L :=
  dgGluingCommaStrictLift R (RightModule R D) (RightModule R C) F KZ L
    (moduleConeInr R D rf) (moduleConeInr R C lf)
    (dgGluingKernelConeInr_square R C D M Y Z f)

/-- 入力成分は、元の右代表加群円錐の同じ右包含。 -/
lemma dgGluingKernelConeInr_source :
    (dgFunctorCommaSource R (RightModule R D) (RightModule R C) F).onClosed.map
      (dgGluingKernelConeInr R C D M Y Z f) = moduleConeInr R D rf :=
  dgGluingCommaStrictLift_source R (RightModule R D) (RightModule R C) F KZ L _ _ _

/-- 比較対象成分も、元の左代表加群円錐の同じ右包含。 -/
lemma dgGluingKernelConeInr_replacement :
    (dgFunctorCommaReplacement R (RightModule R D) (RightModule R C) F).onClosed.map
      (dgGluingKernelConeInr R C D M Y Z f) = moduleConeInr R C lf :=
  dgGluingCommaStrictLift_replacement R (RightModule R D) (RightModule R C) F KZ L _ _ _

/-- この厳密包含の第三 cochain は厳密に零。 -/
lemma dgGluingKernelConeInr_comparison :
    dgFunctorCommaHomComparison R (RightModule R D) (RightModule R C) F KZ L
      (𝟙_ (Complex R))
      (ForgetEnrichment.homTo (Complex R) (dgGluingKernelConeInr R C D M Y Z f)) = 0 :=
  dgGluingCommaStrictLift_comparison R (RightModule R D) (RightModule R C) F KZ L _ _ _

end SerrePositivity.InfinityCategories
