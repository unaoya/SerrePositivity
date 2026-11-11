module
public import SerrePositivity.KST.SConstruction.DGIdentityInverseRotationModuleAxes
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingShiftedLeftAxis
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationRestrictedAxes
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationModuleInput
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConePrecomp
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransTransport

/-!
概要：元実逆回転全比較と実 cone 全入力を元始域へ回収する。
方針：元全軸等号を前合成し同じ全 cone・shift 族へ接続する。
規約：元始域・元全 Hom・指定 shift を保持する。
使われ方：元実 gluing cone 全 realization 比較と同じ全実逆回転比較の接続。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  {P : Type (max (u + 1) v)} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "I" => DGFunctor.id C
local notation "M" => dgHomGluingBimodule R C C C (I) (I)
local notation "H" => dgIdentityHomGluingFunctor R C F G a h

local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C C (M)
local notation "family" => dgHomGluingLoopConeFamily R C C C (I) (I)
local notation "J" => dgSmallPerfectEnvelopeInclusion R C ((L) ⊕ (L)) (family)
local notation "K" => dgPerfectModuleUnderlying R C (J)
local notation "Loop" => dgHomGluingLoopConeSmall R C C C (I) (I)
local notation "DS" => dgHomGluingLoopConeShiftedTarget R C C C (I) (I)
local notation "B" => dgIdentityHomGluingModuleConeFamily R C F G a h
local notation "FS" => DGFunctor.comp (F.comp (dgYoneda R C)) (moduleShiftDG R C 1)
local notation "S" => moduleShiftDG R C (-1)

local notation "η" => dgIdentityInverseRotationImageComparison R C
local notation "β" => dgIdentityHomGluingConeConnectingComparison R C F G a h
local notation "βs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (β) (S)

/-- 概要：元始域へ制限した実像逆回転全比較は元 connecting の逆 shift。
方針：両全軸と元実閉射を型付きで回収する。
規約：元全厳密比較を保持。使われ方：同じ実 cone 入力全族への接続。 -/
lemma dgIdentityHomGluingInverseRotationImageComparison_restriction :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp (H) (η)) (βs) := by
  apply dgModuleStrictNatTrans_heq_of_arrow_heq R C _ _ _ _ _ (βs)
    (dgIdentityHomGluingInverseRotationImageSource_restriction R C F G a h)
    (dgIdentityHomGluingInverseRotationImageTarget_restriction R C F G a h)
  intro x
  have ha := dgIdentityInverseRotationImageComparison_arrow R C ((H).obj x)
  have hb := dgIdentityHomGluingInverseRotationModuleArrow R C F G a h x
  exact heq_of_eq (ha.trans hb.symm)

/-- 概要：元実像逆回転 cone 全族の制限は元実 connecting cone 全族。
方針：同じ cone の全前合成と全厳密入力の型付き一致を使用する。
規約：対象別同値で代用しない。使われ方：元実逆回転全比較の合成。 -/
lemma dgIdentityHomGluingInverseRotationImageConeFamily_restriction :
    (H).comp (dgIdentityInverseRotationImageConeFamily R C) =
      dgIdentityHomGluingInverseRotationModuleSource R C F G a h := by
  exact (dgModuleNaturalConeFunctor_precomp R C ((Loop).comp (K)) ((DS).comp (K)) (η) (H)).trans
    (dgModuleNaturalConeFunctor_eq_of_heq R C _ _ _ _ _ (βs)
      (dgIdentityHomGluingInverseRotationImageSource_restriction R C F G a h)
      (dgIdentityHomGluingInverseRotationImageTarget_restriction R C F G a h)
      (dgIdentityHomGluingInverseRotationImageComparison_restriction R C F G a h))
end SerrePositivity.KST.SConstruction
