module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeShiftComparisonNative
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConnectingConeCompositeNative
public import SerrePositivity.KST.SConstruction.DGModuleShiftCancellationSpecifiedComposite

/-!
概要：同じ元 connecting cone 比較の実逆 shift と指定相殺を全厳密合成する。
方針：元 cone shift 逆比較・元全合成比較の逆 shift・同じ指定相殺を合成する。
規約：元の全 Hom 作用・指定成分を保持する。
使われ方：実逆回転後の全比較を元厳密比較族上に構成する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "FS" => F.comp (moduleShiftDG R D 1)
local notation "GS" => G.comp (moduleShiftDG R D 1)
local notation "δ" => dgModuleNaturalConeConnecting R D F G η
local notation "CD" => dgModuleNaturalConeFunctor R D (CF) (FS) (δ)
local notation "S" => moduleShiftDG R D (-1)

/-- 概要：元逆 shift connecting 射の同じ実 cone 族。
方針：元 connecting の全比較を実 dg shift して元 cone 関手へ渡す。
規約：元零化・元実 cone を保持。使われ方：実逆回転全比較の始域。 -/
def dgModuleNaturalInverseRotationSource : DGFunctor R P (RightModule R D) :=
  dgModuleNaturalConeFunctor R D ((CF).comp (S)) ((FS).comp (S))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (δ) (S))

/-- 概要：同じ元 cone shift の全逆比較。方針：元全比較を適用。
規約：元実成分不変。使われ方：全逆回転の第一因子。 -/
def dgModuleNaturalInverseRotationConeShift : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
    (dgModuleNaturalInverseRotationSource R D F G η) ((CD).comp (S)) :=
  dgModuleNaturalConeShiftComparison R D (CF) (FS) (δ) (-1)

/-- 概要：同じ元全 connecting 比較の逆 shift。方針：元 dg shift 後合成。
規約：元全比較不変。使われ方：全逆回転の第二因子。 -/
def dgModuleNaturalInverseRotationShiftedComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans ((CD).comp (S)) ((GS).comp (S)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (dgModuleNaturalConnectingConeComposite R D F G η) (S)

/-- 概要：同じ元指定相殺の入力制限。方針：元全 Hom 比較を入力関手の同じ斉次作用へ制限。
規約：元相殺成分を保持。使われ方：全逆回転の第三因子。 -/
def dgModuleNaturalInverseRotationCancellation : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans ((GS).comp (S)) G where
  app x := (dgModuleSpecifiedCancellationStrictComparison R D).app (G.obj x)
  naturality z := (dgModuleSpecifiedCancellationStrictComparison R D).naturality
    ((G.map _ _).f _ z)

/-- 概要：元実逆回転後の cone から元第二関手への全厳密比較。
方針：同じ元 cone shift 比較、同じ全 connecting 比較の逆 shift、指定相殺を合成。
規約：点ごとの同値選択を使わず元全比較を保持する。
使われ方：実商合成全比較の逆回転因子。 -/
def dgModuleNaturalInverseRotation : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
    (dgModuleNaturalInverseRotationSource R D F G η) G :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp
      (dgModuleNaturalInverseRotationConeShift R D F G η)
      (dgModuleNaturalInverseRotationShiftedComparison R D F G η))
    (dgModuleNaturalInverseRotationCancellation R D G)
end SerrePositivity.KST.SConstruction
