module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingRealizedConeNative
public import SerrePositivity.KST.SConstruction.DGHomGluingInverseRotation
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeComparisonRecovery
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence
public import SerrePositivity.KST.SConstruction.DGPerfectModuleUnderlyingComposition

/-!
概要：元実逆回転の二実像小模型で元 cone の realization 全比較を具体化する。
方針：元逆回転関手の二軸・元比較・同じ包絡包含を指定評価全比較へ代入する。
規約：元実 gluing cone・元逆回転射・全 Hom を保持する。
使われ方：元始域へ制限した実逆回転後の合成全比較。
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

/-- 概要：元実逆回転小模型の元比較を同じ実加群像の全比較へ送る。
方針：元二軸と元全比較を同じ評価 square の構成子へ渡す。
規約：元逆回転閉射を保持。使われ方：実像 cone の入力全比較。 -/
def dgIdentityInverseRotationImageComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (F0) (G0) :=
  dgIdentityHomGluingRealizedModuleComparison R E (U) (J) (F) (G) (a) (h)
local notation "η" => dgIdentityInverseRotationImageComparison R E

/-- 概要：元実像比較の閉射は元実逆回転加群射そのもの。
方針：同じ二段の充満持ち上げの包含後回収を使用する。
規約：元実射の厳密等式。使われ方：元 connecting 逆 shift と全比較の入力照合。 -/
lemma dgIdentityInverseRotationImageComparison_arrow (x : L) :
    dgModuleNaturalConeArrow R E (F0) (G0) (η) x =
      dgHomGluingInverseRotationModuleMap R E E E (I) (I) x :=
  (dgIdentityHomGluingRealizedModuleComparison_arrow R E (U) (J) (F) (G) (a) (h) x).trans
    (dgSmallPerfectEnvelopeComparisonMap_module R E ((L) ⊕ (L)) (family)
      (dgHomGluingLoopConeFunctor R E E E (I) (I))
      (dgHomGluingDoubleShiftLeftFunctor R E E E (I) (I))
      Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl)
      (dgHomGluingInverseRotationModuleMap R E E E (I) (I)) x)

/-- 概要：元実逆回転 gluing cone 関手の同じ実 realization 族。
方針：元逆回転関手・元 cone 関手・同じ二実像評価を合成する。
規約：元全関手を保持。使われ方：指定合成全比較の元 cone 始域。 -/
def dgIdentityInverseRotationRealizedConeFamily : DGFunctor R (L) (RightModule R E) :=
  (dgPerfectModuleUnderlying R (U)
    ((dgHomGluingInverseRotationFunctor R E E E (I) (I)).comp
      (dgHomGluingConeFunctor R (U) (U) (U) (IU) (IU)))).comp (V)

/-- 概要：同じ元実像逆回転射を入力とする実 cone の全族。
方針：元実像の全厳密比較を元 cone 関手へ渡す。
規約：元閉射・全 Hom を保持。使われ方：全実逆回転比較の入力 cone 族。 -/
def dgIdentityInverseRotationImageConeFamily : DGFunctor R (L) (RightModule R E) :=
  dgModuleNaturalConeFunctor R E (F0) (G0) (η)

/-- 概要：元実逆回転 gluing cone の realization と元実像 cone の全比較。
方針：同じ元逆回転データを元評価・cone image・全 square 比較へ代入する。
規約：元実 cone と元実逆回転射を保持。
使われ方：元始域の全実逆回転比較と固定 ν の指定上下二単体への接続。 -/
def dgIdentityInverseRotationRealizedConeNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityInverseRotationRealizedConeFamily R E))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityInverseRotationImageConeFamily R E)) :=
  dgIdentityHomGluingRealizedConeNerveComparison R E (U) (J) (F) (G) (a) (h)

/-- 概要：元実像 cone の左軸は元 loop cone の全加群像。
方針：同じ二実像包含の全回収と関手結合則を使用する。
規約：元全関手の等号。使われ方：元始域への制限後の全入力照合。 -/
lemma dgIdentityInverseRotationImageSource :
    (F0) = dgPerfectModuleUnderlying R E (dgHomGluingLoopConeFunctor R E E E (I) (I)) :=
  dgPerfectModuleUnderlying_comp_of_eq R E (F) (J)
    (dgHomGluingLoopConeFunctor R E E E (I) (I))
    (dgHomGluingLoopConeSmall_inclusion R E E E (I) (I))

/-- 概要：元実像 cone の右軸は元二重 shift 左成分の全加群像。
方針：同じ二実像包含の全回収と関手結合則を使用する。
規約：元全関手の等号。使われ方：指定相殺を保つ全逆回転入力照合。 -/
lemma dgIdentityInverseRotationImageTarget :
    (G0) = dgPerfectModuleUnderlying R E
      (dgHomGluingDoubleShiftLeftFunctor R E E E (I) (I)) :=
  dgPerfectModuleUnderlying_comp_of_eq R E (G) (J)
    (dgHomGluingDoubleShiftLeftFunctor R E E E (I) (I))
    (dgHomGluingLoopConeShiftedTarget_inclusion R E E E (I) (I))
end SerrePositivity.KST.SConstruction
