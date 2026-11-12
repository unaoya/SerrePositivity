module
public import SerrePositivity.KST.SConstruction.DGIdentityInverseRotationRealization
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingRealizedConeInputBoundary

/-!
概要：元恒等 gluing の実逆回転全評価に元右包含と指定代表評価を保持する。
方針：元二軸・元実逆回転射を同じ実 cone 全比較の包含回収へ代入する。
規約：元全関手・元実包含・同じ評価同型を変更しない。
使われ方：元始域への制限と固定 ν の上指定二単体の接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E : Type (max (u + 1) v))
  [DGCategory R E] [Small.{u} E]
local notation "I" => DGFunctor.id E
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R E E (dgHomGluingBimodule R E E E (I) (I))
local notation "U" => DGHomGluingLoopConeBase R E E E (I) (I)
local notation "IU" => DGFunctor.id (U)
local notation "family" => dgHomGluingLoopConeFamily R E E E (I) (I)
local notation "J" => dgSmallPerfectEnvelopeInclusion R E ((L) ⊕ (L)) (family)
local notation "V" => dgPerfectRealization R (U) E (J)
local notation "F" => dgHomGluingLoopConeSmall R E E E (I) (I)
local notation "G" => dgHomGluingLoopConeShiftedTarget R E E E (I) (I)
local notation "a" => dgHomGluingInverseRotationMap R E E E (I) (I)
local notation "h" => dgHomGluingInverseRotationMap_hom_naturality R E E E (I) (I)
local notation "K" => dgPerfectModuleUnderlying R E (J)
local notation "F0" => DGFunctor.comp (F) (K)
local notation "G0" => DGFunctor.comp (G) (K)

local notation "GY" => DGFunctor.comp (G) (dgYoneda R (U))
local notation "GYV" => DGFunctor.comp (GY) (V)
local notation "η" => dgIdentityInverseRotationImageComparison R E

/-- 概要：元実逆回転 cone の右包含の同じ実 tensor 評価像。
方針：元実入力同型で回収した元包含を同じ realization で後合成する。
規約：元包含を保持。使われ方：元上指定二単体の実評価側の辺。 -/
def dgIdentityInverseRotationRealizedConeInr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (GYV) (dgIdentityInverseRotationRealizedConeFamily R E) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp
    (dgIdentityHomGluingModuleConeInr R (U) (F) (G) (a) (h)) (V)

/-- 概要：同じ元実像逆回転射の cone における元右包含。
方針：同じ元全比較と元二軸の自然 cone 包含を取る。
規約：元実像射を保持。使われ方：元全評価比較の包含終辺。 -/
def dgIdentityInverseRotationImageConeInr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (G0) (dgIdentityInverseRotationImageConeFamily R E) :=
  dgModuleNaturalConeInr R E (F0) (G0) (η)

/-- 概要：元右軸の同じ代表加群評価を全厳密比較として保持する。
方針：元指定小模型包含の代表評価を元右軸で制限する。
規約：指定評価射を保持。使われ方：元実逆回転全比較の右包含境界。 -/
def dgIdentityInverseRotationTargetEvaluation : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (GYV) (G0) :=
  dgPerfectRealizationYonedaRestrictedStrictComparison R E (U) (J) (G)

/-- 概要：元実逆回転の全評価比較は元包含と同じ右軸評価に可換。
方針：元入力逆と元評価 square の全包含回収を特殊化する。
規約：全関手射の等号。使われ方：元上指定二単体の二段実評価への接続。 -/
lemma dgIdentityInverseRotationRealizedConeNerveComparison_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (L) (RightModule R E)
        (dgIdentityInverseRotationRealizedConeInr R E) ≫
      (dgIdentityInverseRotationRealizedConeNerveComparison R E).hom =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (L) (RightModule R E)
          (dgIdentityInverseRotationTargetEvaluation R E) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (L) (RightModule R E)
            (dgIdentityInverseRotationImageConeInr R E) :=
  dgIdentityHomGluingRealizedConeNerveComparison_inr R E (U) (J) (F) (G) (a) (h)
end SerrePositivity.KST.SConstruction
