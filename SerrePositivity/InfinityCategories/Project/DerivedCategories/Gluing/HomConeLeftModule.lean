module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeLeftAugmentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeModule

/-! 左係数を、全 dg 自然な同じ cone 比較加群射の実 Hom 後合成へ移す。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

lemma dgGluingYoneda_postcompose_inv (x : C) {U V : RightModule R C}
    (g : ForgetEnrichment.of (Complex R) U ⟶ ForgetEnrichment.of (Complex R) V) :
    (moduleEvaluation R C x).map g ≫ (dgYonedaIso R x V).inv =
    (dgYonedaIso R x U).inv ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (representable R x)) g := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_postcompose R C x g
  apply (cancel_mono (dgYonedaIso R x V).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, hn, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "B" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y
local notation "C'" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z
local notation "cf" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)) f
local notation "U" => ForgetEnrichment.to (Complex R)
  (moduleCone R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M B C' cf))
local notation "V" => ForgetEnrichment.to (Complex R)
  (moduleCone R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M B C' cf))

/-- 左 Hom cone を、同じ左射の実 cone 加群からの全 Hom と同定する。 -/
def dgGluingHomConeLeftModuleIso :
    mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftArrow R C D M X Y Z f) ≅
      moduleHom R C (representable R X.left) U :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftSourceIso R C D M X Y Z f ≪≫ (dgYonedaIso R X.left U).symm

/-- 双加群作用の cone を、同じ右像の cone 加群からの全 Hom と同定する。 -/
def dgGluingHomConeImageModuleIso :
    mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeAction R C D M X Y Z f) ≅
      moduleHom R C (representable R X.left) V :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftTargetIso R C D M X Y Z f ≪≫ (dgYonedaIso R X.left V).symm

/-- 左係数は同じ全 dg 自然な cone 比較加群射の後合成の負に一致する。 -/
lemma dgGluingHomConeLeftCoefficient_module :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftCoefficient R C D M X Y Z f ≫
      (dgGluingHomConeImageModuleIso R C D M X Y Z f).hom =
    -((dgGluingHomConeLeftModuleIso R C D M X Y Z f).hom ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (representable R X.left))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeMorphism R C D M Y Z f)) := by
  have he := dgGluingYoneda_postcompose_inv R C X.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeMorphism R C D M Y Z f)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaConeMorphism_eval] at he
  simp only [dgGluingHomConeImageModuleIso, dgGluingHomConeLeftModuleIso,
    Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftCoefficient_augmentation,
    Preadditive.neg_comp, Category.assoc]
  erw [he]
  rw [← Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
