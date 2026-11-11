module
public import SerrePositivity.KST.SConstruction.DGModuleShiftComparisonNaturality
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeArrowComp
public import SerrePositivity.KST.SConstruction.DGModuleInverseRotationCone

/-!
概要：元二重 shift の指定相殺を全厳密比較として保持する。
方針：元加法同型の逆と零 shift 同型の全 Hom 自然性を合成する。
規約：元実相殺同型の成分を変更しない。
使われ方：実逆回転後の合成全比較の終辺。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：元零 shift 同型の全厳密自然比較。
方針：元全 Hom 自然性を束ねる。規約：元閉成分を保持。
使われ方：指定相殺の第二因子。 -/
def dgModuleShiftZeroStrictComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (moduleShiftDG R D 0) (DGFunctor.id (RightModule R D)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R D
    (fun M => (moduleShiftZeroIsoObj R D M).hom) (dgModuleShiftZeroHomNaturality R D)

/-- 概要：元加法 shift 同型の逆の全厳密自然比較。
方針：指定同型の全 Hom 自然性の逆律を使用。
規約：元二重 shift を保持。使われ方：指定相殺の第一因子。 -/
def dgModuleShiftAddInvStrictComparison (s t : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans ((moduleShiftDG R D s).comp (moduleShiftDG R D t))
      (moduleShiftDG R D (s + t)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R D
    (fun M => (moduleShiftAddIsoObj R D s t M).inv)
    (dgFunctorClosedComparison_inv_naturality R
      (moduleShiftDG R D (s + t))
      ((moduleShiftDG R D s).comp (moduleShiftDG R D t))
      (moduleShiftAddIsoObj R D s t) (dgModuleShiftAddHomNaturality R D s t))

/-- 概要：同じ元 shift 1・逆 shift の実相殺を持つ全厳密比較。
方針：元加法同型の逆と零 shift 同型を全厳密合成する。
規約：元相殺成分を保持。使われ方：実逆回転後の全比較の終辺。 -/
def dgModuleShiftCancellationStrictComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans ((moduleShiftDG R D 1).comp (moduleShiftDG R D (-1)))
      (DGFunctor.id (RightModule R D)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (dgModuleShiftAddInvStrictComparison R D 1 (-1))
    (dgModuleShiftZeroStrictComparison R D)
end SerrePositivity.KST.SConstruction
