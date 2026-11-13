module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.KernelConeRightArrow
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.KernelClosedReflection

/-! 選んだ円錐対象への native gluing の実閉射と、その二代表加群成分。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R C Y.left Z.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f))
  (q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)))
local notation "F" => Morita.kernelTensor R D C M
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "a" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeRepresentativeMap R C D M Y Z f p q
local notation "i" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeInr R C D M Y Z f

/-- 標準円錐の右包含を同じ代表射で移し、native gluing に回収した実閉射。 -/
def dgGluingConeInr : ForgetEnrichment.of (Complex R) Z ⟶
    ForgetEnrichment.of (Complex R) W :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelClosedPreimage R C D M Z W (i ≫ a)

/-- 円錐包含の kernel 像は、標準包含と同じ円錐代表射の合成。 -/
lemma dgGluingConeInr_kernel :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M).onClosed.map
      (dgGluingConeInr R C D M Y Z f p q) = i ≫ a :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelClosedPreimage_map R C D M Z W (i ≫ a)

/-- 入力成分は元の右代表加群円錐の包含を同じ代表射で送ったもの。 -/
lemma dgGluingConeInr_kernel_source :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R (RightModule R D) (RightModule R C) F).onClosed.map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M).onClosed.map
        (dgGluingConeInr R C D M Y Z f p q)) =
    moduleConeInr R D ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRepresentativeHom R D Y.right Z.right
        ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)) q := by
  rw [dgGluingConeInr_kernel, CategoryTheory.Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeInr_source, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeRepresentativeMap,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaBoundaryLift_source]

/-- 比較対象成分も、元の左代表加群円錐の包含を同じ代表射で送ったもの。 -/
lemma dgGluingConeInr_kernel_replacement :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R (RightModule R D) (RightModule R C) F).onClosed.map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M).onClosed.map
        (dgGluingConeInr R C D M Y Z f p q)) =
    moduleConeInr R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRepresentativeHom R C Y.left Z.left
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f) p := by
  rw [dgGluingConeInr_kernel, CategoryTheory.Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeInr_replacement, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeRepresentativeMap,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaBoundaryLift_replacement]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
