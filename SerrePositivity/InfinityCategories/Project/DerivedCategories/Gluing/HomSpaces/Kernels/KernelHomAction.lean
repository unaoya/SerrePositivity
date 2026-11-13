module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.Kernels.KernelColumnHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.ActionYoneda
public import SerrePositivity.DifferentialGraded.Endomorphism.Shift

/-! 試験 gluing 対象の augmentation を通常 kernel tensor へ持ち上げた全 Hom 作用。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 試験対象の同じ augmentation を、右代表加群の tensor 像へ持ち上げる。 -/
def dgGluingKernelLift :
    ForgetEnrichment.of (Complex R) (representable R X.left) ⟶
      (Morita.kernelTensor R D C M).onClosed.obj
        (ForgetEnrichment.of (Complex R) (representable R X.right)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) X.right)).inv

/-- 同じ通常 kernel の全 Hom 写像と試験対象の augmentation による作用。 -/
def dgGluingKernelHomAction (N : RightModule R D) :
    moduleHom R D (representable R X.right) N ⟶
      moduleHom R C (representable R X.left) ((Morita.kernelTensor R D C M).obj N) :=
  (Morita.kernelTensor R D C M).map (representable R X.right) N ≫
    eHomWhiskerRight (Complex R) (dgGluingKernelLift R C D M X)
      (ForgetEnrichment.of (Complex R) ((Morita.kernelTensor R D C M).obj N))

/-- 全 Hom 作用は右加群の閉零射の後合成と可換。 -/
lemma dgGluingKernelHomAction_postcompose {N N' : ClosedCategory R (RightModule R D)}
    (f : N ⟶ N') :
    eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (representable R X.right)) f ≫
        dgGluingKernelHomAction R C D M X N' =
    dgGluingKernelHomAction R C D M X N ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (representable R X.left))
        ((Morita.kernelTensor R D C M).onClosed.map f) := by
  dsimp only [dgGluingKernelHomAction]
  have hn := dgHomMap_postcompose (Morita.kernelTensor R D C M)
    (ForgetEnrichment.of (Complex R) (representable R X.right)) f
  erw [← Category.assoc, hn, Category.assoc, eHom_whisker_exchange]
  rfl

/-- 代表加群上でこの作用を評価すると、元の右双加群作用そのものを回収する。 -/
lemma dgGluingKernelHomAction_yoneda (Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    yonedaHom R D X.right Y.right ≫
      dgGluingKernelHomAction R C D M X (representable R Y.right) ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (representable R X.left))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).hom ≫
      (dgYonedaIso R X.left (M.rightAt Y.right)).hom =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y := by
  dsimp only [dgGluingKernelHomAction]
  simp only [Category.assoc]
  erw [← eHom_whisker_exchange_assoc]
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso_hom_naturality R C D M X.right Y.right
  rw [← Category.assoc] at hn
  erw [← Category.assoc, ← Category.assoc, hn, Category.assoc, Category.assoc]
  change M.toFunctor.map X.right Y.right ≫
    eHomWhiskerRight (Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) X.right)).hom
      (ForgetEnrichment.of (Complex R) (M.rightAt Y.right)) ≫
    eHomWhiskerRight (Complex R) (dgGluingKernelLift R C D M X)
      (ForgetEnrichment.of (Complex R) (M.rightAt Y.right)) ≫
    (dgYonedaIso R X.left (M.rightAt Y.right)).hom = _
  rw [← eHomWhiskerRight_comp_assoc]
  simp only [dgGluingKernelLift, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction_yoneda R C D M X Y

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
