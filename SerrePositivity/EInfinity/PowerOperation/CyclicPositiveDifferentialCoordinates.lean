module

public import SerrePositivity.EInfinity.PowerOperation.CyclicPeriodicRestriction
public import SerrePositivity.EInfinity.PowerOperation.RegularOrbitCoordinates

/-!
# 正の周期 Hom の同じ微分の座標

DAG XIII Construction 2.2.6 の orbit 境界比較の補助。
切り詰めの包含の可換性を使い、元の Hom 微分を指定評価で計算する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CochainComplex HomComplex
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]

/-- 正の部分の指定項同型は、元の周期微分を保つ。 -/
lemma cyclicPositiveResolution_inv_d (i : ℤ) (hi : 0 ≤ i) :
    (StupidTruncation.aboveXIso (powerOperationCompleteResolution p k) 0 i hi).inv ≫
      (cyclicPositiveResolution p k).d i (i + 1) =
    cyclicTateDifferential (Rep.leftRegular k (PowerOperationCyclicGroup.{u} p))
      (powerOperationCyclicGenerator p) i ≫
      (StupidTruncation.aboveXIso (powerOperationCompleteResolution p k) 0 (i + 1)
        (by omega)).inv := by
  have h := (StupidTruncation.inclusion (powerOperationCompleteResolution p k) 0).comm
    i (i + 1)
  rw [StupidTruncation.inclusion_f _ _ _ hi,
    StupidTruncation.inclusion_f _ _ _ (show 0 ≤ i + 1 by omega)] at h
  have h' := congrArg (fun f =>
    (StupidTruncation.aboveXIso (powerOperationCompleteResolution p k) 0 i hi).inv ≫ f ≫
      (StupidTruncation.aboveXIso (powerOperationCompleteResolution p k) 0 (i + 1)
        (by omega)).inv) h
  simp only [Iso.inv_hom_id_assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id] at h'
  simpa [cyclicPositiveResolution, powerOperationCompleteResolution,
    cyclicTateComplex, CochainComplex.of.d]
    using h'.symm

variable (M : CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ)

/-- 切り詰めの同じ項同型を使った、指定した一座標の評価。 -/
def cyclicPositiveHomCoordinate {n : ℤ}
    (z : Cochain (cyclicPositiveResolution p k) M n)
    (i j : ℤ) (hij : i + n = j) (hi : 0 ≤ i) : M.X j :=
  Rep.leftRegularHomEquiv (M.X j)
    ((StupidTruncation.aboveXIso (powerOperationCompleteResolution p k) 0 i hi).inv ≫
      z.v i j hij)

/-- Hom の同じ周期微分の前合成を、同じ係数微分へ送る。 -/
lemma cyclicPositiveHomCoordinate_periodic
    (i : ℤ) (A : Rep.{u} k (PowerOperationCyclicGroup.{u} p))
    (z : Rep.leftRegular k (PowerOperationCyclicGroup.{u} p) ⟶ A) :
    Rep.leftRegularHomEquiv A
      (cyclicTateDifferential (Rep.leftRegular k (PowerOperationCyclicGroup.{u} p))
        (powerOperationCyclicGenerator p) i ≫ z) =
    (cyclicTateDifferential A (powerOperationCyclicGenerator p) i).hom
      (Rep.leftRegularHomEquiv A z) := by
  rw [cyclicTateDifferential_natural]
  exact regularHomEvaluation_natural _ z

/-- 同じ Hom 微分の一座標は、係数微分と符号付き周期微分の和。 -/
lemma cyclicPositiveHomCoordinate_delta {n : ℤ}
    (z : Cochain (cyclicPositiveResolution p k) M n)
    (i j : ℤ) (hij : i + (n + 1) = j) (hi : 0 ≤ i) :
    cyclicPositiveHomCoordinate p k M (δ n (n + 1) z) i j hij hi =
    (M.d (j - 1) j).hom
      (cyclicPositiveHomCoordinate p k M z i (j - 1) (by omega) hi) +
    (n + 1).negOnePow •
      (cyclicTateDifferential (M.X j) (powerOperationCyclicGenerator p) i).hom
        (cyclicPositiveHomCoordinate p k M z (i + 1) j (by omega) (by omega)) := by
  change Rep.leftRegularHomEquiv _ (_ ≫ (δ n (n + 1) z).v i j hij) = _
  rw [δ_v n (n + 1) rfl z i j hij (j - 1) (i + 1) rfl rfl]
  simp only [Preadditive.comp_add, Units.smul_def, Preadditive.comp_zsmul,
    map_add, map_zsmul]
  congr 1
  rw [← Category.assoc, cyclicPositiveResolution_inv_d, Category.assoc]
  exact congrArg (fun x => ((n + 1).negOnePow : ℤ) • x)
    (cyclicPositiveHomCoordinate_periodic p k i (M.X j)
      ((StupidTruncation.aboveXIso (powerOperationCompleteResolution p k) 0 (i + 1)
        (by omega)).inv ≫ z.v (i + 1) j (by omega)))

end SerrePositivity.EInfinity.PowerOperation
