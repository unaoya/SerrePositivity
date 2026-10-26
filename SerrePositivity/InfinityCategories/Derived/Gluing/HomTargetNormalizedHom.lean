module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCommaComponents
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaNormalizedHom
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientDirectCylinder
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainIdentityCommaLift
/-!
概要：元終域で正規化した Hom 比較は、元二作用と第三 cochain を厳密に保持する。
方針：元 comma 比較を標準閉射で正規化し、同じ二射影・primitive で照合する。
規約：元 E 内の実 Hom 鎖写像。導来係数への輸送は使わない。
使われ方：実 augmentation prism と係数 path の全族比較の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "TX" => dgGluingHomTargetCommaObject R C D E p q X
local notation "TY" => dgGluingHomTargetCommaObject R C D E p q Y

def dgGluingHomTargetNormalizedHom :
    dgGluingHomComplex R C D M X Y ⟶
      dgFunctorCommaHomComplex R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E (p.obj X.left))
        (dgGluingIdentityCommaObject R E (q.obj Y.right)) :=
  dgGluingHomTargetCommaHomMap R C D E p q X Y ≫
    dgGluingCommaNormalizedHom R D E q TX TY

lemma dgGluingHomTargetNormalizedHom_source :
    dgGluingHomTargetNormalizedHom R C D E p q X Y ≫
      dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E (p.obj X.left))
        (dgGluingIdentityCommaObject R E (q.obj Y.right)) =
    dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y := by
  rw [dgGluingHomTargetNormalizedHom, Category.assoc]
  erw [dgGluingCommaNormalizedHom_source R D E q TX TY]
  change dgGluingHomTargetCommaHomMap R C D E p q X Y ≫
    (dgFunctorCommaSourceHomMap R D E q TX TY ≫ q.map X.right Y.right) ≫
      eHomWhiskerRight (Complex R) (dgHomGluingTargetMap R C D E p q X)
        (ForgetEnrichment.of (Complex R) (q.obj Y.right)) = _
  simp only [Category.assoc]
  rw [← Category.assoc (dgGluingHomTargetCommaHomMap R C D E p q X Y)
    (dgFunctorCommaSourceHomMap R D E q TX TY)]
  erw [dgGluingHomTargetCommaHomMap_source R C D E p q X Y]
  erw [dgGluingHomTarget_rightAction R C D E p q X Y]

lemma dgGluingHomTargetNormalizedHom_replacement :
    dgGluingHomTargetNormalizedHom R C D E p q X Y ≫
      dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E (p.obj X.left))
        (dgGluingIdentityCommaObject R E (q.obj Y.right)) =
    dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y := by
  rw [dgGluingHomTargetNormalizedHom, Category.assoc]
  erw [dgGluingCommaNormalizedHom_replacement R D E q TX TY]
  rw [← Category.assoc, dgGluingHomTargetCommaHomMap_replacement, Category.assoc]
  erw [dgGluingHomTarget_leftAction R C D E p q X Y]

lemma dgGluingHomTargetNormalizedHom_primitive :
    (Cochain.ofHom (dgGluingHomTargetNormalizedHom R C D E p q X Y)).comp
      (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E (p.obj X.left))
        (dgGluingIdentityCommaObject R E (q.obj Y.right))) (zero_add (-1)) =
    dgGluingHomPrimitive R C D M X Y := by
  rw [dgGluingHomTargetNormalizedHom, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [dgGluingCommaNormalizedHom_primitive R D E q TX TY]
  exact dgGluingHomTargetCommaHomMap_comparison R C D E p q X Y

/-- 元終域での正規化は、元の負 primitive の明示 cochain lift に厳密一致する。 -/
lemma dgGluingHomTargetNormalizedHom_eq_cochainLift :
    dgGluingHomTargetNormalizedHom R C D E p q X Y =
      dgGluingCochainIdentityCommaLift R E (p.obj X.left) (q.obj Y.right)
        (dgGluingHomComplex R C D M X Y)
        (dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y)
        (dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y)
        (-dgGluingHomPrimitive R C D M X Y)
        (dgGluingHomNegativePrimitive_boundary R C D M X Y) := by
  apply dgFunctorCommaHom_ext R E E (DGFunctor.id E)
    (dgGluingIdentityCommaObject R E (p.obj X.left))
    (dgGluingIdentityCommaObject R E (q.obj Y.right)) _
  · rw [dgGluingCochainIdentityCommaLift_end, dgGluingHomTargetNormalizedHom_source]
  · rw [dgGluingCochainIdentityCommaLift_start,
      dgGluingHomTargetNormalizedHom_replacement]
  · dsimp only [dgFunctorCommaHomComparison]
    exact (dgGluingHomTargetNormalizedHom_primitive R C D E p q X Y).trans
      ((dgGluingCochainIdentityCommaLift_primitive R E (p.obj X.left) (q.obj Y.right)
        (dgGluingHomComplex R C D M X Y)
        (dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y)
        (dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y)
        (-dgGluingHomPrimitive R C D M X Y)
        (dgGluingHomNegativePrimitive_boundary R C D M X Y)).trans (neg_neg _)).symm

end SerrePositivity.InfinityCategories
