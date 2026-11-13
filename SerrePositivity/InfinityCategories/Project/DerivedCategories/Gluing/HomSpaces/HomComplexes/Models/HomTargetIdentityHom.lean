module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomTargetCommaHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomCalculus
/-! 元二脚の Hom gluing を同じ終域の恒等二脚へ送る全 Hom 比較。
左右 Hom は指定二関手で送り、第三 cochain は同じ元を保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded KST.SConstruction

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)

local notation "M" => dgHomGluingBimodule R C D E p q

local notation "I" => dgHomGluingBimodule R E E E (DGFunctor.id E) (DGFunctor.id E)

def dgGluingHomTargetIdentityObject (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R E E I where
  left := p.obj X.left
  right := q.obj X.right
  gluing := X.gluing

variable (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

local notation "TX" => dgGluingHomTargetIdentityObject R C D E p q X

local notation "TY" => dgGluingHomTargetIdentityObject R C D E p q Y

def dgGluingHomTargetIdentityComponents :
    (homObject R C X.left Y.left ⊞ homObject R D X.right Y.right) ⟶
      (homObject R E (p.obj X.left) (p.obj Y.left) ⊞
        homObject R E (q.obj X.right) (q.obj Y.right)) := by
  exact biprod.lift (biprod.fst ≫ p.map X.left Y.left)
    (biprod.snd ≫ q.map X.right Y.right)

lemma dgGluingHomTargetIdentityComponents_difference :
    dgGluingHomTargetIdentityComponents R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R E E I TX TY = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y := by
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTarget_leftAction R E E E (DGFunctor.id E) (DGFunctor.id E) TX TY
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTarget_rightAction R E E E (DGFunctor.id E) (DGFunctor.id E) TX TY
  simp only [DGFunctor.id, EnrichedFunctor.id_map, Category.id_comp] at hl hr
  change eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) (p.obj X.left))
    (dgHomGluingTargetMap R C D E p q Y) = _ at hl
  change eHomWhiskerRight (Complex R) (dgHomGluingTargetMap R C D E p q X)
    (ForgetEnrichment.of (Complex R) (q.obj Y.right)) = _ at hr
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference, Preadditive.comp_sub,
    dgGluingHomTargetIdentityComponents]
  erw [biprod.lift_snd_assoc, biprod.lift_fst_assoc]
  simp only [Category.assoc, ← hl, ← hr]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTarget_rightAction, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTarget_leftAction]

def dgGluingHomTargetIdentityHomMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R E E I TX TY :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap _ _ (dgGluingHomTargetIdentityComponents R C D E p q X Y)
    (𝟙 _) (by
      rw [Category.comp_id]
      exact (dgGluingHomTargetIdentityComponents_difference R C D E p q X Y).symm)

lemma dgGluingHomTargetIdentityHomMap_left :
    dgGluingHomTargetIdentityHomMap R C D E p q X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R E E I TX TY =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y ≫ p.map X.left Y.left := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap]
  rw [dgGluingHomTargetIdentityHomMap, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst, Category.assoc]
  dsimp only [dgGluingHomTargetIdentityComponents]
  erw [biprod.lift_fst]
  exact (Category.assoc _ _ _).symm

lemma dgGluingHomTargetIdentityHomMap_right :
    dgGluingHomTargetIdentityHomMap R C D E p q X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R E E I TX TY =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y ≫ q.map X.right Y.right := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap]
  rw [dgGluingHomTargetIdentityHomMap, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst, Category.assoc]
  dsimp only [dgGluingHomTargetIdentityComponents]
  erw [biprod.lift_snd]
  exact (Category.assoc _ _ _).symm

lemma dgGluingHomTargetIdentityHomMap_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComparison R E E I TX TY _
      (dgGluingHomTargetIdentityHomMap R C D E p q X Y) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComparison, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive, dgGluingHomTargetIdentityHomMap]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd]
  exact Cochain.comp_id _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
