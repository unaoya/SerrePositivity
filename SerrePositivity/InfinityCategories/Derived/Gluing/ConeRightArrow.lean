module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeRightArrow
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelClosedReflection

/-! 選んだ円錐対象への native gluing の実閉射と、その二代表加群成分。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (p : DGGluingConeRepresentative R C Y.left Z.left (dgGluingConeLeftArrow R C D M Y Z f))
  (q : DGGluingConeRepresentative R D Y.right Z.right
    ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)))
local notation "F" => Morita.kernelTensor R D C M
local notation "W" => dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "a" => dgGluingKernelConeRepresentativeMap R C D M Y Z f p q
local notation "i" => dgGluingKernelConeInr R C D M Y Z f

/-- 標準円錐の右包含を同じ代表射で移し、native gluing に回収した実閉射。 -/
def dgGluingConeInr : ForgetEnrichment.of (Complex R) Z ⟶
    ForgetEnrichment.of (Complex R) W :=
  dgGluingKernelClosedPreimage R C D M Z W (i ≫ a)

/-- 円錐包含の kernel 像は、標準包含と同じ円錐代表射の合成。 -/
lemma dgGluingConeInr_kernel :
    (dgGluingToKernelComma R C D M).onClosed.map
      (dgGluingConeInr R C D M Y Z f p q) = i ≫ a :=
  dgGluingKernelClosedPreimage_map R C D M Z W (i ≫ a)

/-- 入力成分は元の右代表加群円錐の包含を同じ代表射で送ったもの。 -/
lemma dgGluingConeInr_kernel_source :
    (dgFunctorCommaSource R (RightModule R D) (RightModule R C) F).onClosed.map
      ((dgGluingToKernelComma R C D M).onClosed.map
        (dgGluingConeInr R C D M Y Z f p q)) =
    moduleConeInr R D ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)) ≫
      dgGluingConeRepresentativeHom R D Y.right Z.right
        ((dgYoneda R D).onClosed.map (dgGluingConeRightArrow R C D M Y Z f)) q := by
  rw [dgGluingConeInr_kernel, CategoryTheory.Functor.map_comp,
    dgGluingKernelConeInr_source, dgGluingKernelConeRepresentativeMap,
    dgGluingCommaBoundaryLift_source]

/-- 比較対象成分も、元の左代表加群円錐の包含を同じ代表射で送ったもの。 -/
lemma dgGluingConeInr_kernel_replacement :
    (dgFunctorCommaReplacement R (RightModule R D) (RightModule R C) F).onClosed.map
      ((dgGluingToKernelComma R C D M).onClosed.map
        (dgGluingConeInr R C D M Y Z f p q)) =
    moduleConeInr R C (dgGluingConeLeftArrow R C D M Y Z f) ≫
      dgGluingConeRepresentativeHom R C Y.left Z.left
        (dgGluingConeLeftArrow R C D M Y Z f) p := by
  rw [dgGluingConeInr_kernel, CategoryTheory.Functor.map_comp,
    dgGluingKernelConeInr_replacement, dgGluingKernelConeRepresentativeMap,
    dgGluingCommaBoundaryLift_replacement]

end SerrePositivity.InfinityCategories
