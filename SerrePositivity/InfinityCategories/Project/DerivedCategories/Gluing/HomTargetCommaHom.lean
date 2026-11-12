module
public import SerrePositivity.KST.SConstruction.DGHomGluingTargetCone
public import SerrePositivity.KST.SConstruction.DGClosedWhiskerComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaCategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexMappingCoconeMap
/-!
概要：Hom gluing の元の比較を、共通終域の実 comma の対象と Hom に送る。
方針：左右作用を閉比較による前後合成へ照合し、同じ第三 cochain を持つ cocone 写像を作る。
規約：元の終域と両関手を保持し、加群圏上の通常 pullback とは同一視しない。
使われ方：元の Perf 二脚を持つ lax pullback 比較の全単体族の構成に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
open KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
def dgGluingHomTargetCommaObject (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R D E q where
  source := X.right
  replacement := p.obj X.left
  augmentation := dgHomGluingTargetMap R C D E p q X
variable (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "TX" => dgGluingHomTargetCommaObject R C D E p q X
local notation "TY" => dgGluingHomTargetCommaObject R C D E p q Y
lemma dgGluingHomTarget_leftAction :
    p.map X.left Y.left ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (p.obj X.left))
      (dgHomGluingTargetMap R C D E p q Y) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D (dgHomGluingBimodule R C D E
          p q) X Y := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (p.obj X.left))
    (dgHomGluingTargetMap R C D E p q Y)).f n ((p.map X.left Y.left).f n f) = _
  have hw := dgClosedWhiskerLeft_f (A := R) (D := E)
    (x := p.obj X.left) (y := p.obj Y.left) (z := q.obj Y.right)
    (dgHomGluingTargetMap R C D E p q Y) n ((p.map X.left Y.left).f n f)
  rw [hw, dgHomGluingTargetMap]
  erw [Equiv.apply_symm_apply]
  simp only [compose, mul_zero, Int.negOnePow_zero, one_smul]
  exact (dgHomGluingLeftAction_apply R C D E p q X Y n f).symm
lemma dgGluingHomTarget_rightAction :
    q.map X.right Y.right ≫ eHomWhiskerRight (Complex R)
      (dgHomGluingTargetMap R C D E p q X)
      (ForgetEnrichment.of (Complex R) (q.obj Y.right)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D
          (dgHomGluingBimodule R C D E p q) X Y := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (eHomWhiskerRight (Complex R) (dgHomGluingTargetMap R C D E p q X)
    (ForgetEnrichment.of (Complex R) (q.obj Y.right))).f n ((q.map X.right Y.right).f n f) = _
  have hw := dgClosedWhiskerRight_f (A := R) (D := E)
    (x := p.obj X.left) (y := q.obj X.right) (z := q.obj Y.right)
    (dgHomGluingTargetMap R C D E p q X) n ((q.map X.right Y.right).f n f)
  rw [hw, dgHomGluingTargetMap]
  erw [Equiv.apply_symm_apply]
  simp only [compose, zero_mul, Int.negOnePow_zero, one_smul]
  exact (dgHomGluingRightAction_apply R C D E p q X Y n f).symm
def dgGluingHomTargetCommaComponents :
    (homObject R C X.left Y.left ⊞ homObject R D X.right Y.right) ⟶
      (homObject R D X.right Y.right ⊞ homObject R E (p.obj X.left) (p.obj Y.left)) :=
  biprod.lift biprod.snd (biprod.fst ≫ p.map X.left Y.left)
lemma dgGluingHomTargetCommaComponents_difference :
    dgGluingHomTargetCommaComponents R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R D E q (TX) (TY) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D (dgHomGluingBimodule R
          C D E p q) X Y := by
  simp only [dgGluingHomTargetCommaComponents, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference,
    dgGluingHomTargetCommaObject, Preadditive.comp_sub]
  erw [biprod.lift_fst_assoc, biprod.lift_snd_assoc]
  simp only [Category.assoc]
  rw [dgGluingHomTarget_rightAction, dgGluingHomTarget_leftAction]
  rfl
def dgGluingHomTargetCommaHomMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D (dgHomGluingBimodule R C D E p q) X Y ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R D
        E q (TX) (TY) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D (dgHomGluingBimodule R C D E p q) X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R D E q (TX) (TY))
    (dgGluingHomTargetCommaComponents R C D E p q X Y) (𝟙 _) (by
      rw [Category.comp_id]
      exact (dgGluingHomTargetCommaComponents_difference R C D E p q X Y).symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
