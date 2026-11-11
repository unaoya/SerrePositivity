module
public import SerrePositivity.KST.SConstruction.DGModuleShiftCancellationRecovery

/-!
概要：元 shift 相殺の加法次数を先に輸送し、同じ指定成分を保持する。
方針：整数の和を加群型の展開前に零へ輸送する。
規約：元加法・零 shift 同型を使用する。
使われ方：実逆回転全比較の指定相殺。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
private lemma transportedAddArrow (s t q : ℤ) (h : s + t = q) (M : RightModule R D) :
    dgModuleNaturalConeArrow R D ((moduleShiftDG R D s).comp (moduleShiftDG R D t))
      (moduleShiftDG R D q) (h ▸ dgModuleShiftAddInvStrictComparison R D s t) M =
      (h ▸ moduleShiftAddIsoObj R D s t M).inv := by
  cases h
  exact dgModuleShiftAddInvStrictComparison_arrow R D s t M

/-- 概要：同じ元加法逆比較の次数零への明示輸送。
方針：加群型を展開せず整数和を先に輸送する。
規約：元比較を保持。使われ方：指定相殺の第一因子。 -/
def dgModuleShiftAddInvSpecifiedComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans ((moduleShiftDG R D 1).comp (moduleShiftDG R D (-1)))
      (moduleShiftDG R D 0) :=
  (show (1 : ℤ) + (-1) = 0 from rfl) ▸ dgModuleShiftAddInvStrictComparison R D 1 (-1)

/-- 概要：同じ元加法同型の始域次数零への明示輸送。
方針：同じ整数和の輸送を使用。
規約：元実同型を保持。使われ方：元指定相殺の成分回収。 -/
def dgModuleShiftAddSpecifiedIso (M : RightModule R D) :
    ForgetEnrichment.of (Complex R) (shiftModule 0 M) ≅
      ForgetEnrichment.of (Complex R) (shiftModule (-1) (shiftModule 1 M)) :=
  (show (1 : ℤ) + (-1) = 0 from rfl) ▸ moduleShiftAddIsoObj R D 1 (-1) M

/-- 概要：次数を先に輸送した同じ全比較は元指定加法逆射を回収する。
方針：一般の次数輸送で閉射回収を先に証明する。
規約：元成分不変。使われ方：指定相殺合成の閉射回収。 -/
lemma dgModuleShiftAddInvSpecifiedComparison_arrow (M : RightModule R D) :
    dgModuleNaturalConeArrow R D
      ((moduleShiftDG R D 1).comp (moduleShiftDG R D (-1))) (moduleShiftDG R D 0)
      (dgModuleShiftAddInvSpecifiedComparison R D) M = (dgModuleShiftAddSpecifiedIso R D M).inv :=
  transportedAddArrow R D 1 (-1) 0 rfl M
end SerrePositivity.KST.SConstruction
