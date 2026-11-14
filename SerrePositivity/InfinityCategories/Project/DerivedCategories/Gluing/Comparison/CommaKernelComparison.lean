module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.KernelColumnComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.Kernels.KernelHomIdentity
public import Mathlib.CategoryTheory.Enriched.HomCongr

/-! 双加群値 comma の対象と全 Hom を、同じ通常 kernel の加群 comma に送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "F" => Morita.kernelTensor R D C M
local notation "col" d =>
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) d)

/-- 右成分を Yoneda で送り、同じ augmentation を列比較の逆射で持ち上げる。 -/
def dgGluingCommaKernelObject (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R D (RightModule R C) M.toFunctor) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
      (Morita.kernelTensor R D C M) where
  source := representable R X.source
  replacement := X.replacement
  augmentation := X.augmentation ≫ (col X.source).inv

variable (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
local notation "B" => dgGluingCommaKernelObject R C D M X
local notation "T" => dgGluingCommaKernelObject R C D M Y

/-- 係数 Hom の列同型は、閉同型による通常の豊穣 Hom 同型。 -/
def dgGluingCommaKernelTargetIso :
    homObject R (RightModule R C) X.replacement (M.toFunctor.obj Y.source) ≅
    homObject R (RightModule R C) X.replacement ((F).obj (representable R Y.source)) :=
  Iso.eHomCongr (Complex R)
    (Iso.refl (ForgetEnrichment.of (Complex R) X.replacement)) (col Y.source).symm

lemma dgGluingCommaKernelTargetIso_hom :
    (dgGluingCommaKernelTargetIso R C D M X Y).hom =
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
        (col Y.source).inv := by
  simp [dgGluingCommaKernelTargetIso, Iso.eHomCongr]

/-- 二成分と係数 Hom の列同型は、元の同じ比較差を保つ。 -/
lemma dgGluingCommaKernelDifference :
    (biprod.mapIso (dgYonedaIso R X.source (representable R Y.source)).symm
      (Iso.refl (homObject R (RightModule R C) X.replacement Y.replacement))).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R (RightModule R D) (RightModule R C) F B T =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R D (RightModule R C) M.toFunctor X Y ≫
      (dgGluingCommaKernelTargetIso R C D M X Y).hom := by
  simp only [biprod.mapIso_hom, Iso.refl_hom, Iso.symm_hom,
    dgGluingCommaKernelTargetIso_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]
  erw [biprod.map_fst_assoc, biprod.map_snd_assoc]
  simp only [Category.id_comp]
  apply congrArg₂ (fun a b => a - b)
  · simp only [dgGluingCommaKernelObject, eHomWhiskerRight_comp]
    have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso_inv_naturality R C D M X.source Y.source
    have he := congrArg (fun k =>
      (biprod.fst :
        (homObject R D X.source Y.source ⊞
          homObject R (RightModule R C) X.replacement Y.replacement) ⟶ _) ≫ k ≫
        eHomWhiskerRight (Complex R) X.augmentation
          (ForgetEnrichment.of (Complex R) ((F).obj (representable R Y.source)))) hn.symm
    simp only [Category.assoc] at he
    erw [eHom_whisker_exchange (Complex R) X.augmentation (col Y.source).inv] at he
    exact he
  · simp only [dgGluingCommaKernelObject, eHomWhiskerLeft_comp]
    rfl

/-- 元の comma 全 Hom と kernel comma 全 Hom の実鎖同型。 -/
def dgGluingCommaKernelHomIso :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R D (RightModule R C) M.toFunctor X Y ≅
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F B T :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMapIso _ _
    (biprod.mapIso (dgYonedaIso R X.source (representable R Y.source)).symm (Iso.refl _))
    (dgGluingCommaKernelTargetIso R C D M X Y)
    (dgGluingCommaKernelDifference R C D M X Y).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
