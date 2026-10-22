module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelHomEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelCommaObjects

/-! 元の gluing Hom と、同じ二つの代表加群の kernel comma Hom との実鎖同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y : DGGluingObject R C D M)
local notation "F" => Morita.kernelTensor R D C M
local notation "B" => dgGluingKernelObject R C D M X
local notation "T" => dgGluingKernelObject R C D M Y
local notation "d" => dgFunctorCommaDifference R (RightModule R D) (RightModule R C) F B T

/-- kernel 表示の augmentation による左作用を評価すると、元の左作用の列同型による移送。 -/
lemma dgGluingKernelLeftAction_evaluate :
    yonedaHom R C X.left Y.left ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (representable R X.left))
        (dgGluingKernelLift R C D M Y) ≫
      (dgYonedaIso R X.left ((F).obj (representable R Y.right))).hom =
    dgGluingLeftAction R C D M X Y ≫ (moduleEvaluation R C X.left).map
      (dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).inv := by
  have hn := dgGluingYoneda_postcompose R C X.left
    (dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).inv
  simp only [dgGluingKernelLift, eHomWhiskerLeft_comp, Category.assoc]
  erw [hn]
  have he := dgGluingLeftAction_yoneda R C D M X Y
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
    (dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right))).symm ≪≫
    (dgYonedaIso R X.left ((F).obj (representable R Y.right))).symm

/-- 比較差は、同じ列同型と両側の全 Yoneda Hom 写像で厳密に可換する。 -/
lemma dgGluingKernelHomDifference_evaluate :
    (dgGluingKernelHomComponentsIso R C D M X Y).hom ≫ d ≫
      (dgYonedaIso R X.left ((F).obj (representable R Y.right))).hom =
    dgGluingDifference R C D M X Y ≫ (moduleEvaluation R C X.left).map
      (dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Y.right)).inv := by
  rw [dgGluingKernelHomComponentsIso_hom]
  simp only [dgFunctorCommaDifference, dgGluingKernelObject, Preadditive.comp_sub,
    Preadditive.sub_comp, Category.assoc]
  erw [biprod.lift_fst_assoc, biprod.lift_snd_assoc]
  simp only [Category.assoc]
  have hr := dgGluingKernelHomAction_evaluate R C D M X Y
  dsimp only [dgGluingKernelHomAction] at hr
  simp only [Category.assoc] at hr
  erw [hr, dgGluingKernelLeftAction_evaluate R C D M X Y]
  simp only [dgGluingDifference, Preadditive.sub_comp, Category.assoc]

/-- 元の実 Hom 複体と、同じ代表加群・持ち上げた augmentation の kernel Hom との実鎖同型。 -/
def dgGluingKernelHomIso : dgGluingHomComplex R C D M X Y ≅
    dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F B T :=
  complexMappingCoconeMapIso (dgGluingDifference R C D M X Y) d
    (dgGluingKernelHomComponentsIso R C D M X Y) (dgGluingKernelHomTargetIso R C D M X Y) (by
      apply (cancel_mono (dgYonedaIso R X.left ((F).obj (representable R Y.right))).hom).1
      simp only [dgGluingKernelHomTargetIso, Iso.trans_hom, Iso.symm_hom,
        CategoryTheory.Functor.mapIso_inv,
        Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact (dgGluingKernelHomDifference_evaluate R C D M X Y).symm)

end SerrePositivity.InfinityCategories
