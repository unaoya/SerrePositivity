module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Size
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeRightArrow
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelRepresentativeHomotopy

/-! native 円錐包含の全 dg 自然な Yoneda 加群射と、その同じ kernel 表示。 -/
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
local notation "W" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObjectFromRepresentatives R C D M Y Z f p q
local notation "i" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInr R C D M Y Z f p q
local notation "KX" X => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M X

/-- 円錐包含の Yoneda 像は、gluing 上の全 dg 自然な右加群の実閉射。 -/
def dgGluingConeInrModuleMap :
    ForgetEnrichment.of (Complex R) (representable R Z) ⟶
      ForgetEnrichment.of (Complex R) (representable R W) :=
  (dgYoneda R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)).onClosed.map i

/-- 各試験対象での評価は、元の native 円錐包含による同じ実 Hom 後合成。 -/
lemma dgGluingConeInrModuleMap_eval (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (moduleEvaluation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X).map
      (dgGluingConeInrModuleMap R C D M Y Z f p q) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Z W i :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_evaluate R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X Z W i

/-- 同じ加群射の評価を kernel 表示で読むと、標準包含と代表射の二つの後合成。 -/
lemma dgGluingConeInrModuleMap_kernel (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Z W i ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M X W).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M X Z).hom ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (KX X))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeInr R C D M Y Z f) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeRepresentativePost R C D M Y Z f p q (KX X) := by
  have he := dgHomMap_postcompose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M)
    (ForgetEnrichment.of (Complex R) X) i
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInr_kernel,
    eHomWhiskerLeft_comp] at he
  exact he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
