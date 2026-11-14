module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZeroLeibniz
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyCupGradedRing
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyCupGradedRing
public import SerrePositivity.CommutativeAlgebra.DeRham.Graded
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZeroLeibniz
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZero

/-!
# affine Hodge–Tate コホモロジーの微分代数

## 概要
余単体のコホモロジーと Bockstein に次数付き可換微分代数の構造を与える。

## 方針
cup 積の斉次環を使い、係数の作用と Bockstein の積公式を照合する。

## 規約
微分代数の係数環は基底の剰余環。affine 多項式係数には Bockstein が作用する。

## 使われ方
多項式 de Rham 代数の普遍性による Hodge–Tate 写像。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
  (hP : IsBoundedPrism P) (r : ℕ)

local notation "X" => reducedModel P hP r
local notation "H" => hodgeTateCohomology' P hP r
local notation "k" => A ⧸ P.ideal
local notation "R" => affineAlgebra P r

local instance (i : ℕ) : Module R (H i) := htModule P hP r i
local instance (i : ℕ) : Module k (H i) := Module.compHom _ (algebraMap k R)

private theorem bockstein_cast {i j : ℕ} (e : i = j) (x : H i) :
    bockstein P hP r j (cast (congrArg (H) e) x) =
      cast (congrArg (fun n => H (n+1)) e) (bockstein P hP r i x) := by
  subst j
  rfl

private theorem htCastZero {i j : ℕ} (e : i = j) :
    cast (congrArg (H) e) (0 : H i) = 0 := by
  subst j
  rfl

private theorem cup_zero_left_zero (Y : CosimplicialObject CommRingCat.{u})
    (i j : ℕ) (z : cohomology Y j) : cohomologyCup Y (0 : cohomology Y i) z = 0 :=
  (cohomologyCupGradedRing Y).zero_mul z

set_option maxHeartbeats 1000000 in
-- 余単体模型の作用を零次 cup 積で読み、Bockstein の次数の変換を照合する。
set_option backward.isDefEq.respectTransparency false in
private theorem bockstein_smul_base (n : ℕ) (a : k) (x : H n) :
    bockstein P hP r n (a • x) = a • bockstein P hP r n x := by
  let f := algebraMap k R a
  let z := hodgeTateMapZero P hP r f
  let β := bockstein P hP r
  change β n (f • x) = f • β n x
  have hf₀ : f • x = cast (congrArg (H) (Nat.zero_add n)) (cohomologyCup X z x) :=
    (htModuleData P hP r n).property f x
  have hf₁ : f • β n x = cast (congrArg (H) (Nat.zero_add (n+1))) (cohomologyCup X z (β n x)) :=
    (htModuleData P hP r (n+1)).property f _
  have hz : β 0 z = 0 := htBocksteinZero_algebraMap P hP r a
  have h := bockstein_leibniz (htRings P hP r) (htGenerator P hP r) (htGenerator_nat P hP r)
    (htGenerator_regular P hP r) A (htBase P hP r) 0 n z x
  dsimp only at h
  change β (0+n) (cohomologyCup X z x) =
    cast (congrArg (H) (by omega : 1+n = 0+n+1)) (cohomologyCup X (β 0 z) x) +
      (1 : ℤ) • cohomologyCup X z (β n x) at h
  rw [hz, cup_zero_left_zero, htCastZero, one_zsmul, zero_add (cohomologyCup X z (β n x))] at h
  have hc := congrArg (cast (congrArg (fun t => H (t+1)) (Nat.zero_add n))) h
  rw [hf₀, hf₁]
  exact (bockstein_cast P hP r (Nat.zero_add n) (cohomologyCup X z x)).trans hc
  all_goals omega

private def htBaseD (i : ℕ) : H i →ₗ[k] H (i+1) where
  toAddHom := bockstein P hP r i
  map_smul' a x := bockstein_smul_base P hP r i a x

private theorem htHeq {i j : ℕ} (e : i = j)
    {x : H i} {y : H j} (h : cast (congrArg (H) e) x = y) : HEq x y := by
  subst j
  exact heq_of_eq h

local instance : DirectSum.GRing (H) := cohomologyCupGradedRing X

private def etaBase : k →+* H 0 :=
  (hodgeTateMapZero P hP r).comp (algebraMap k R)

set_option maxHeartbeats 1400000 in
-- 零次の係数射と各次数の cup 積を照合する。
set_option backward.isDefEq.respectTransparency false in
@[instance_reducible] private def htBaseGradedAlgebra : DirectSum.GAlgebra k (H) where
  toFun := (etaBase P hP r).toAddMonoidHom
  map_one := map_one (etaBase P hP r)
  map_mul a b := Sigma.ext rfl (heq_of_eq (by
    change etaBase P hP r (a*b) = cohomologyCup X (etaBase P hP r a) (etaBase P hP r b)
    rw [etaBase, RingHom.comp_apply, map_mul, etaZero_mul]
    rfl))
  commutes a z := Sigma.ext (Nat.zero_add z.1) (htHeq P hP r (Nat.zero_add z.1) (by
    change cast (congrArg (H) (Nat.add_comm 0 z.1)) (cohomologyCup X (etaBase P hP r a) z.2) =
      cohomologyCup X z.2 (etaBase P hP r a)
    simpa only [Nat.zero_mul, pow_zero, one_zsmul] using
      cohomologyCup_comm X (etaBase P hP r a) z.2))
  smul_def a z := Sigma.ext (Nat.zero_add z.1).symm
    (HEq.symm (htHeq P hP r (Nat.zero_add z.1) ((htModuleData P hP r z.1).property
      (algebraMap k R a) z.2).symm))

/-- affine Hodge–Tate コホモロジーに Bockstein の微分を入れた次数付き代数。 -/
def htGradedDGAlgebra : SerrePositivity.DeRham.GradedCommDGAlgebra k where
  carrier := H
  gradedAlgebra := htBaseGradedAlgebra P hP r
  d := htBaseD P hP r
  d_sq i x := cupBockstein_sq (htRings P hP r) (htGenerator P hP r)
    (htGenerator_nat P hP r) (htGenerator_regular P hP r) A (htBase P hP r) i x
  mul_comm := cohomologyCup_comm X
  leibniz := fun x y => bockstein_leibniz (htRings P hP r) (htGenerator P hP r)
    (htGenerator_nat P hP r) (htGenerator_regular P hP r) A (htBase P hP r) _ _ x y

end SerrePositivity.BhattScholze.Prismatic
