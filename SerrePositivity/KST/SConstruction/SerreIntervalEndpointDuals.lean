module
public import SerrePositivity.KST.SConstruction.SerreIntervalDualCoordinates

/-! # 元の二端点の双対座標
概要：元の零・一端点に対する双対座標を、元の単位成分と境界成分から回収する。
方針：元の disk 上側生成元が一端点と零端点の差であることを使う。
規約：元の区間・二端点・辺を保持。使われ方：元の次数零の任意の線形射の復元。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の disk 上側生成元の区間内の像は、元の一端点と零端点の差。 -/
lemma serreInterval_upper_eq_endpoints :
    (biprod.inr : complexDisk A (-1) ⟶ serreInterval A).f 0
        ((complexDiskX₁ A (-1)).inv 1) =
      (cycleFromUnit _ (serreIntervalOne A)).val -
        (cycleFromUnit _ (serreIntervalZero A)).val := by
  have h := complexDisk_upper_apply A (-1)
    (biprod.inr : complexDisk A (-1) ⟶ serreInterval A)
  exact h.trans (serreIntervalEdge_d A)

/-- 元の一端点の単位成分は一。 -/
lemma serreIntervalUnitCoordinate_one :
    serreIntervalUnitCoordinate A (cycleFromUnit _ (serreIntervalOne A)).val = 1 := by
  have h := congrArg (fun w => serreIntervalUnitCoordinate A w)
    (serreInterval_upper_eq_endpoints A)
  rw [serreIntervalUnitCoordinate_upper, map_sub, serreIntervalUnitCoordinate_zero] at h
  exact sub_eq_zero.mp h.symm

/-- 元の一端点の境界成分は一。 -/
lemma serreIntervalBoundaryCoordinate_one :
    serreIntervalBoundaryCoordinate A (cycleFromUnit _ (serreIntervalOne A)).val = 1 := by
  have h := congrArg (fun w => serreIntervalBoundaryCoordinate A w)
    (serreInterval_upper_eq_endpoints A)
  rw [serreIntervalBoundaryCoordinate_upper, map_sub, serreIntervalBoundaryCoordinate_zero,
    sub_zero] at h
  exact h.symm

/-- 元の零端点に対応する双対座標。元の一端点では零になる。 -/
def serreIntervalZeroCoordinate : (serreInterval A).X 0 ⟶ 𝟙_ (ModuleCat A) :=
  serreIntervalUnitCoordinate A - serreIntervalBoundaryCoordinate A

/-- 元の零端点の零端点双対座標は一。 -/
lemma serreIntervalZeroCoordinate_zero :
    serreIntervalZeroCoordinate A (cycleFromUnit _ (serreIntervalZero A)).val = 1 := by
  change serreIntervalUnitCoordinate A _ - serreIntervalBoundaryCoordinate A _ = 1
  rw [serreIntervalUnitCoordinate_zero, serreIntervalBoundaryCoordinate_zero, sub_zero]

/-- 元の一端点の零端点双対座標は零。 -/
lemma serreIntervalZeroCoordinate_one :
    serreIntervalZeroCoordinate A (cycleFromUnit _ (serreIntervalOne A)).val = 0 := by
  change serreIntervalUnitCoordinate A _ - serreIntervalBoundaryCoordinate A _ = 0
  rw [serreIntervalUnitCoordinate_one, serreIntervalBoundaryCoordinate_one, sub_self]

end SerrePositivity.KST.SConstruction
