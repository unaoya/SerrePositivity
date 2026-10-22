module
public import SerrePositivity.InfinityCategories.Derived.Gluing.Size
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeRightArrow
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelRepresentativeHomotopy

/-! native 円錐包含の全 dg 自然な Yoneda 加群射と、その同じ kernel 表示。 -/
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
local notation "W" => dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "i" => dgGluingConeInr R C D M Y Z f p q
local notation "KX" X => dgGluingKernelObject R C D M X

/-- 円錐包含の Yoneda 像は、gluing 上の全 dg 自然な右加群の実閉射。 -/
def dgGluingConeInrModuleMap :
    ForgetEnrichment.of (Complex R) (representable R Z) ⟶
      ForgetEnrichment.of (Complex R) (representable R W) :=
  (dgYoneda R (DGGluingObject R C D M)).onClosed.map i

/-- 各試験対象での評価は、元の native 円錐包含による同じ実 Hom 後合成。 -/
lemma dgGluingConeInrModuleMap_eval (X : DGGluingObject R C D M) :
    (moduleEvaluation R (DGGluingObject R C D M) X).map
      (dgGluingConeInrModuleMap R C D M Y Z f p q) =
    dgGluingPostcomposition R C D M X Z W i :=
  dgGluingYoneda_evaluate R (DGGluingObject R C D M) X Z W i

/-- 同じ加群射の評価を kernel 表示で読むと、標準包含と代表射の二つの後合成。 -/
lemma dgGluingConeInrModuleMap_kernel (X : DGGluingObject R C D M) :
    dgGluingPostcomposition R C D M X Z W i ≫
      (dgGluingKernelHomIso R C D M X W).hom =
    (dgGluingKernelHomIso R C D M X Z).hom ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (KX X))
        (dgGluingKernelConeInr R C D M Y Z f) ≫
      dgGluingKernelConeRepresentativePost R C D M Y Z f p q (KX X) := by
  have he := dgHomMap_postcompose (dgGluingToKernelComma R C D M)
    (ForgetEnrichment.of (Complex R) X) i
  rw [dgGluingToKernelComma_map, dgGluingToKernelComma_map, dgGluingConeInr_kernel,
    eHomWhiskerLeft_comp] at he
  exact he

end SerrePositivity.InfinityCategories
