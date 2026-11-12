module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelHomEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelCommaObjects

/-! 元の gluing Hom と、同じ二つの代表加群の kernel comma Hom との実鎖同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "F" => Morita.kernelTensor R D C M
local notation "B" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M X
local notation "T" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M Y
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R (RightModule R D) (RightModule R C) F B T

/-- kernel 表示の augmentation による左作用を評価すると、元の左作用の列同型による移送。 -/
lemma dgGluingKernelLeftAction_evaluate :
    yonedaHom R C X.left Y.left ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (representable R X.left))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelLift R C D M Y) ≫
      (dgYonedaIso R X.left ((F).obj (representable R Y.right))).hom =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y ≫ (moduleEvaluation R C X.left).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).inv := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_postcompose R C X.left
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).inv
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelLift, eHomWhiskerLeft_comp, Category.assoc]
  erw [hn]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction_yoneda R C D M X Y
  rw [← Category.assoc] at he
  erw [← Category.assoc, ← Category.assoc, he]

/-- 元の左右 Hom を、両側の Yoneda により kernel comma の同じ順の二成分へ送る。 -/
def dgGluingKernelHomComponentsIso :
    (homObject R C X.left Y.left ⊞ homObject R D X.right Y.right) ≅
    (moduleHom R D (representable R X.right) (representable R Y.right) ⊞
      moduleHom R C (representable R X.left) (representable R Y.left)) :=
  biprod.braiding _ _ ≪≫ biprod.mapIso
    (dgYonedaIso R X.right (representable R Y.right)).symm
    (dgYonedaIso R X.left (representable R Y.left)).symm

lemma dgGluingKernelHomComponentsIso_hom :
    (dgGluingKernelHomComponentsIso R C D M X Y).hom =
    biprod.lift (biprod.snd ≫ yonedaHom R D X.right Y.right)
      (biprod.fst ≫ yonedaHom R C X.left Y.left) := by
  apply biprod.hom_ext <;>
    simp [dgGluingKernelHomComponentsIso, biprod.braiding, yonedaHom]

/-- 元の双加群値と、同じ右代表加群の tensor 像への全 Hom との列比較同型。 -/
def dgGluingKernelHomTargetIso : M.value X.left Y.right ≅
    moduleHom R C (representable R X.left) ((F).obj (representable R Y.right)) :=
  ((moduleEvaluation R C X.left).mapIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right))).symm ≪≫
    (dgYonedaIso R X.left ((F).obj (representable R Y.right))).symm

/-- 比較差は、同じ列同型と両側の全 Yoneda Hom 写像で厳密に可換する。 -/
lemma dgGluingKernelHomDifference_evaluate :
    (dgGluingKernelHomComponentsIso R C D M X Y).hom ≫ d ≫
      (dgYonedaIso R X.left ((F).obj (representable R Y.right))).hom =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y ≫ (moduleEvaluation R C X.left).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).inv := by
  rw [dgGluingKernelHomComponentsIso_hom]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject, Preadditive.comp_sub,
    Preadditive.sub_comp, Category.assoc]
  erw [biprod.lift_fst_assoc, biprod.lift_snd_assoc]
  simp only [Category.assoc]
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction_evaluate R C D M X Y
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction] at hr
  simp only [Category.assoc] at hr
  erw [hr, dgGluingKernelLeftAction_evaluate R C D M X Y]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference, Preadditive.sub_comp, Category.assoc]

/-- 元の実 Hom 複体と、同じ代表加群・持ち上げた augmentation の kernel Hom との実鎖同型。 -/
def dgGluingKernelHomIso : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y ≅
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F B T :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y) d
    (dgGluingKernelHomComponentsIso R C D M X Y) (dgGluingKernelHomTargetIso R C D M X Y) (by
      apply (cancel_mono (dgYonedaIso R X.left ((F).obj (representable R Y.right))).hom).1
      simp only [dgGluingKernelHomTargetIso, Iso.trans_hom, Iso.symm_hom,
        CategoryTheory.Functor.mapIso_inv,
        Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact (dgGluingKernelHomDifference_evaluate R C D M X Y).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
