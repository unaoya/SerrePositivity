module

public import SerrePositivity.EInfinity.PowerOperation.CyclicOrbitFiniteCoordinates
public import SerrePositivity.EInfinity.PowerOperation.CyclicOrbitCoordinateSign
public import SerrePositivity.EInfinity.PowerOperation.CyclicPositiveFiniteCoordinates

/-!
# 正の周期 Hom と orbit 全複体の符号付き次数同型

DAG XIII Construction 2.2.6 の鎖模型比較の補助。
同じ有限座標に ε_s = (-1)^{binom(s,2)} を掛ける。
ここで構成するのは各次数の指定同型であり、微分との可換性は別に示す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CochainComplex HomComplex
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]
variable (M : CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ)
    (d : ℤ) [M.IsStrictlyLE d] (n : ℤ)

/-- 同じ有限座標の指定符号による自己同値。 -/
def cyclicOrbitFiniteSignEquiv :
    (∀ s : {s : ℤ // s ∈ Finset.Icc 0 (d - n)}, M.X (s.1 + n)) ≃ₗ[k]
      ∀ s : {s : ℤ // s ∈ Finset.Icc 0 (d - n)}, M.X (s.1 + n) where
  toFun x s := cyclicOrbitCoordinateSign s.1.toNat • x s
  invFun x s := cyclicOrbitCoordinateSign s.1.toNat • x s
  left_inv x := by
    funext s
    change cyclicOrbitCoordinateSign s.1.toNat •
      (cyclicOrbitCoordinateSign s.1.toNat • x s) = x s
    rw [smul_smul, cyclicOrbitCoordinateSign_sq, one_smul]
  right_inv x := by
    funext s
    change cyclicOrbitCoordinateSign s.1.toNat •
      (cyclicOrbitCoordinateSign s.1.toNat • x s) = x s
    rw [smul_smul, cyclicOrbitCoordinateSign_sq, one_smul]
  map_add' x y := by
    funext s
    exact smul_add _ _ _
  map_smul' r x := by
    funext s
    exact smul_comm _ r _

/-- 元の正の周期 Hom と元の orbit 直和全複体の、同じ次数の実同型。 -/
def cyclicPositiveOrbitDegreeIso :
    ((cyclicPositiveResolutionHomFunctor p k).obj M).X n ≅
      ((cyclicOrbitTotalFunctor p k).obj M).X n :=
  (cyclicPositiveFiniteCoordinates p k M d n).toModuleIso ≪≫
    (cyclicOrbitFiniteSignEquiv p k M d n).toModuleIso ≪≫
    (cyclicOrbitTotalDegreeCoordinatesIso p k M d n).symm

end SerrePositivity.EInfinity.PowerOperation
