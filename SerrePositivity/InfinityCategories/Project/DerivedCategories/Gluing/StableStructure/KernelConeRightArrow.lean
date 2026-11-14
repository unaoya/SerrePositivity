module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.KernelConeInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CommaComparisons.CommaStrictLift

/-! 標準加群円錐への、第三 cochain 零の実閉 kernel comma 包含。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "F" => Morita.kernelTensor R D C M
local notation "KZ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M Z
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeObject R C D M Y Z f
local notation "lf" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f
local notation "rf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgYoneda R D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)

/-- 同じ二つの加群円錐の右包含からなる、標準 kernel 円錐への閉射。 -/
def dgGluingKernelConeInr : ForgetEnrichment.of (Complex R) KZ ⟶
    ForgetEnrichment.of (Complex R) L :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaStrictLift R (RightModule R D) (RightModule R C) F KZ L
    (moduleConeInr R D rf) (moduleConeInr R C lf)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeInr_square R C D M Y Z f)

/-- 入力成分は、元の右代表加群円錐の同じ右包含。 -/
lemma dgGluingKernelConeInr_source :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R (RightModule R D) (RightModule R C) F).onClosed.map
      (dgGluingKernelConeInr R C D M Y Z f) = moduleConeInr R D rf :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaStrictLift_source R (RightModule R D) (RightModule R C) F KZ L _ _ _

/-- 比較対象成分も、元の左代表加群円錐の同じ右包含。 -/
lemma dgGluingKernelConeInr_replacement :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R (RightModule R D) (RightModule R C) F).onClosed.map
      (dgGluingKernelConeInr R C D M Y Z f) = moduleConeInr R C lf :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaStrictLift_replacement R (RightModule R D) (RightModule R C) F KZ L _ _ _

/-- この厳密包含の第三 cochain は厳密に零。 -/
lemma dgGluingKernelConeInr_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R (RightModule R D) (RightModule R C) F KZ L
      (𝟙_ (Complex R))
      (ForgetEnrichment.homTo (Complex R) (dgGluingKernelConeInr R C D M Y Z f)) = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaStrictLift_comparison R (RightModule R D) (RightModule R C) F KZ L _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
