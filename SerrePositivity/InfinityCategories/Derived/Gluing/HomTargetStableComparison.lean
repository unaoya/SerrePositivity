module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxVertices
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeStability
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedFunctorExact
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.LocalizingInvariants
open KST.SConstruction
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [IsDGPretriangulated R C] [IsDGPretriangulated R D] [IsDGPretriangulated R E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q

/-- 元の native nerve をそのまま安定圏に束ねる。 -/
def dgGluingHomTargetStableInput (U : Type (max (u + 1) v)) [DGCategory R U]
    [Small.{u} U] [IsDGPretriangulated R U] : StableCategory.{max (u + 1) v} :=
  ⟨dgNerve R U, inferInstance, dgNerve_isStable_of_pretriangulated R U⟩

def dgGluingHomTargetLeftMap :
    ExactMap (dgGluingHomTargetStableInput R C) (dgGluingHomTargetStableInput R E) :=
  ⟨dgNerve.map p, dgPretriangulatedFunctor_isExactFunctor R C E p⟩

def dgGluingHomTargetRightMap :
    ExactMap (dgGluingHomTargetStableInput R D) (dgGluingHomTargetStableInput R E) :=
  ⟨dgNerve.map q, dgPretriangulatedFunctor_isExactFunctor R D E q⟩

/-- 元 gluing から元終域上の lax pullback への指定比較は完全。 -/
lemma dgGluingHomTargetNerveLaxComparison_isExactFunctor :
    IsExactFunctor (dgGluingHomTargetNerveLaxComparison R C D E p q) := by
  let := dgGluing_isDGPretriangulated R C D M inferInstance inferInstance
  have hL := dgPretriangulatedFunctor_isExactFunctor R
    (DGGluingObject R C D M) C (dgGluingLeft R C D M)
  have hR := dgPretriangulatedFunctor_isExactFunctor R
    (DGGluingObject R C D M) D (dgGluingRight R C D M)
  let P := dgGluingHomTargetLeftMap R C E p
  let Q := dgGluingHomTargetRightMap R D E q
  let F := dgGluingHomTargetNerveLaxComparison R C D E p q
  have : IsExactFunctor (F ≫ (laxFst P Q).hom) :=
    (dgGluingHomTargetNerveLaxComparison_fst R C D E p q).symm ▸ hL
  have : IsExactFunctor (F ≫ (laxSnd P Q).hom) :=
    (dgGluingHomTargetNerveLaxComparison_snd R C D E p q).symm ▸ hR
  exact LaxInclusion.exact_of_components P Q F

/-- 元二脚と元比較辺全族を持つ、同じ完全比較。 -/
def dgGluingHomTargetStableComparison :
    ExactMap
      (⟨dgNerve R (DGGluingObject R C D M), inferInstance,
        dgGluingNerve_isStable R C D M inferInstance inferInstance⟩ : StableCategory)
      (laxCategory (dgGluingHomTargetLeftMap R C E p)
        (dgGluingHomTargetRightMap R D E q)) :=
  ⟨dgGluingHomTargetNerveLaxComparison R C D E p q,
    dgGluingHomTargetNerveLaxComparison_isExactFunctor R C D E p q⟩

end SerrePositivity.InfinityCategories
