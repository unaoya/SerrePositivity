module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetLaxVertices
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeStability
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedFunctorExact
public import SerrePositivity.KST.LocalizingInvariants.LaxInclusionExact
/-!
概要：元二脚の Hom gluing 比較は、元の前三角性から完全関手になる。
方針：元の dg 関手と両射影の完全性を、lax pullback の成分判定へ渡す。
規約：元の比較写像は変更せず、完全性や生成条件を新しい入力にしない。
使われ方：元二脚・恒等二脚の全 cone 比較を安定圏内で構成する入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet KST.LocalizingInvariants
open KST.SConstruction
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q

/-- 元の native nerve をそのまま安定圏に束ねる。 -/
def dgGluingHomTargetStableInput (U : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R U]
    [Small.{u} U] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R U] : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R U, inferInstance, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated R U⟩

def dgGluingHomTargetLeftMap :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgGluingHomTargetStableInput R C) (dgGluingHomTargetStableInput R E) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map p, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedFunctor_isExactFunctor R C E p⟩

def dgGluingHomTargetRightMap :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgGluingHomTargetStableInput R D) (dgGluingHomTargetStableInput R E) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map q, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedFunctor_isExactFunctor R D E q⟩

/-- 元 gluing から元終域上の lax pullback への指定比較は完全。 -/
lemma dgGluingHomTargetNerveLaxComparison_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNerveLaxComparison R C D E p q) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R C D M inferInstance inferInstance
  have hL := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedFunctor_isExactFunctor R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M)
  have hR := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedFunctor_isExactFunctor R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M)
  let P := dgGluingHomTargetLeftMap R C E p
  let Q := dgGluingHomTargetRightMap R D E q
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNerveLaxComparison R C D E p q
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (F ≫ (laxFst P Q).hom) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNerveLaxComparison_fst R C D E p q).symm ▸ hL
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (F ≫ (laxSnd P Q).hom) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNerveLaxComparison_snd R C D E p q).symm ▸ hR
  exact LaxInclusion.exact_of_components P Q F

/-- 元二脚と元比較辺全族を持つ、同じ完全比較。 -/
def dgGluingHomTargetStableComparison :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
      (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M), inferInstance,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNerve_isStable R C D M inferInstance inferInstance⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory)
      (laxCategory (dgGluingHomTargetLeftMap R C E p)
        (dgGluingHomTargetRightMap R D E q)) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNerveLaxComparison R C D E p q,
    dgGluingHomTargetNerveLaxComparison_isExactFunctor R C D E p q⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
