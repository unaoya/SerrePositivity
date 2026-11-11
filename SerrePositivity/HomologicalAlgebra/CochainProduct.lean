module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# 余鎖積のコホモロジーへの降下

## 概要
符号付き Leibniz 則を満たす係数線形な積はコホモロジーに降りる。

## 方針
余輪体上の積を作り、片方が余境界なら積も余境界であることを示して商へ降ろす。

## 規約
余鎖複体は自然数で添字付け、右因子を微分する項の符号は左因子の次数で決める。

## 使われ方
多項式 de Rham 外積と pd 総複体の Alexander–Whitney 積。
-/

public noncomputable section

open CategoryTheory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.HomologicalAlgebra

variable {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℕ)

/-- Leibniz 則を満たす斉次な余鎖積。 -/
structure CochainProduct where
  mul (i j : ℕ) : K.X i →ₗ[R] K.X j →ₗ[R] K.X (i + j)
  leibniz (i j : ℕ) (x : K.X i) (y : K.X j) :
    K.d (i + j) (i + j + 1) (mul i j x y) =
      cast (congrArg (fun n => (K.X n : Type u)) (show (i + 1) + j = (i + j) + 1 by omega))
        (mul (i + 1) j (K.d i (i + 1) x) y) +
      (-1 : ℤ)^i • mul i (j + 1) x (K.d j (j + 1) y)

namespace CochainProduct

variable {K} (M : CochainProduct K)

private abbrev Z (n : ℕ) := LinearMap.ker (K.sc n).g.hom
private abbrev B (n : ℕ) := (K.sc n).moduleCatToCycles.range

private theorem cast_zero' {a b : ℕ} (h : a = b) :
    cast (congrArg (fun n => (K.X n : Type u)) h) (0 : K.X a) = 0 := by
  subst b
  rfl

private theorem cast_d {a b a' b' : ℕ} (h : a = a') (h' : b = b') (x : K.X a) :
    K.d a' b' (cast (congrArg (fun n => (K.X n : Type u)) h) x) =
      cast (congrArg (fun n => (K.X n : Type u)) h') (K.d a b x) := by
  subst a' b'
  rfl

private theorem cycle_d {n : ℕ} (z : Z (K := K) n) : K.d n (n + 1) z.1 = 0 := by
  have hz : (K.sc n).g z.1 = 0 := z.2
  change K.d n ((ComplexShape.up ℕ).next n) z.1 = 0 at hz
  rwa [CochainComplex.next] at hz

private def cycleMul {i j : ℕ} (x : Z (K := K) i) (y : Z (K := K) j) : Z (K := K) (i + j) :=
  ⟨M.mul i j x.1 y.1, by
    change K.d (i + j) ((ComplexShape.up ℕ).next (i + j)) (M.mul i j x.1 y.1) = 0
    rw [CochainComplex.next, M.leibniz, cycle_d x, cycle_d y, map_zero, LinearMap.zero_apply,
      map_zero, smul_zero, add_zero,
      cast_zero' (K := K) (by omega : i + 1 + j = i + j + 1)]⟩

private theorem cycleMul_sub_left {i j : ℕ} (x y : Z (K := K) i) (z : Z (K := K) j) :
    M.cycleMul (x-y) z = M.cycleMul x z - M.cycleMul y z := by
  apply Subtype.ext
  change M.mul i j (x.1-y.1) z.1 = _
  simp only [map_sub, LinearMap.sub_apply, Submodule.coe_sub, cycleMul]

private theorem cycleMul_sub_right {i j : ℕ} (x : Z (K := K) i) (y z : Z (K := K) j) :
    M.cycleMul x (y-z) = M.cycleMul x y - M.cycleMul x z := by
  apply Subtype.ext
  exact map_sub (M.mul i j x.1) y.1 z.1

private theorem zero_prev (n : ℕ) :
    (ComplexShape.up ℕ).prev n = n-1 := by
  cases n with
  | zero => exact CochainComplex.prev_nat_zero
  | succ n => exact CochainComplex.prev_nat_succ n

private theorem bound_rep {n : ℕ} (x : Z (K := K) n) (hx : x ∈ B (K := K) n) :
    ∃ a : K.X (n-1), K.d (n-1) n a = x.1 := by
  obtain ⟨a, ha⟩ := hx
  change K.X ((ComplexShape.up ℕ).prev n) at a
  have h : K.d ((ComplexShape.up ℕ).prev n) n a = x.1 := congrArg Subtype.val ha
  refine ⟨cast (congrArg (fun j => (K.X j : Type u)) (zero_prev n)) a, ?_⟩
  rw [cast_d (zero_prev n) rfl]
  exact h

private theorem bound_of_rep {n : ℕ} (x : Z (K := K) n) (a : K.X (n-1))
    (h : K.d (n-1) n a = x.1) : x ∈ B (K := K) n := by
  refine ⟨cast (congrArg (fun j => (K.X j : Type u)) (zero_prev n).symm) a, Subtype.ext ?_⟩
  change K.d ((ComplexShape.up ℕ).prev n) n _ = x.1
  rw [cast_d (zero_prev n).symm rfl]
  exact h

private theorem bound_zero (x : Z (K := K) 0) (hx : x ∈ B (K := K) 0) :
    x = 0 := by
  obtain ⟨a, ha⟩ := bound_rep x hx
  apply Subtype.ext
  have h : K.d 0 0 = 0 := K.shape _ _ (by decide)
  rw [h] at ha
  exact ha.symm

private theorem left_bound {i j : ℕ} (x : Z (K := K) i) (y : Z (K := K) j)
    (hx : x ∈ B (K := K) i) : M.cycleMul x y ∈ B (K := K) (i + j) := by
  cases i with
  | zero =>
    rw [bound_zero x hx]
    have h : M.cycleMul (0 : Z (K := K) 0) y = 0 := by
      apply Subtype.ext
      change M.mul 0 j 0 y.1 = 0
      rw [map_zero, LinearMap.zero_apply]
    rw [h]
    exact Submodule.zero_mem _
  | succ i =>
    obtain ⟨a, ha⟩ := bound_rep x hx
    change K.d i (i + 1) a = x.1 at ha
    let z := M.mul i j a y.1
    have h := M.leibniz i j a y.1
    rw [cycle_d y, map_zero, smul_zero, add_zero, ha] at h
    have he : (i + 1 + j)-1 = i + j := by omega
    refine bound_of_rep _ (cast (congrArg (fun n => (K.X n : Type u)) he.symm) z) ?_
    change K.d ((i + 1 + j)-1) (i + 1 + j) _ = M.mul (i + 1) j x.1 y.1
    rw [cast_d he.symm (show i + j + 1 = i + 1 + j by omega), h, cast_cast, cast_eq]

private theorem right_bound {i j : ℕ} (x : Z (K := K) i) (y : Z (K := K) j)
    (hy : y ∈ B (K := K) j) : M.cycleMul x y ∈ B (K := K) (i + j) := by
  cases j with
  | zero =>
    rw [bound_zero y hy]
    have h : M.cycleMul x (0 : Z (K := K) 0) = 0 := Subtype.ext (map_zero _)
    rw [h]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨a, ha⟩ := bound_rep y hy
    change K.d j (j + 1) a = y.1 at ha
    have h := M.leibniz i j x.1 a
    rw [cycle_d x, map_zero, LinearMap.zero_apply, ha] at h
    rw [cast_zero' (K := K) (by omega : i + 1 + j = i + j + 1), zero_add] at h
    let z := (-1 : ℤ)^i • M.mul i j x.1 a
    have he : (i + (j + 1))-1 = i + j := by omega
    refine bound_of_rep _ (cast (congrArg (fun n => (K.X n : Type u)) he.symm) z) ?_
    change K.d (i + j) (i + j + 1) z = M.mul i (j + 1) x.1 y.1
    rw [show z = (-1 : ℤ)^i • M.mul i j x.1 a from rfl, map_zsmul, h, smul_smul,
      ← mul_pow]
    simp

private def quotientMul {i j : ℕ} (x : Z (K := K) i ⧸ B (K := K) i)
    (y : Z (K := K) j ⧸ B (K := K) j) : Z (K := K) (i + j) ⧸ B (K := K) (i + j) :=
  Quotient.liftOn₂ x y (fun a b => Submodule.Quotient.mk (M.cycleMul a b))
    (fun a b a' b' ha hb => by
      apply (Submodule.Quotient.eq _).mpr
      have h₁ := M.left_bound (a-a') b ((Submodule.quotientRel_def _).mp ha)
      have h₂ := M.right_bound a' (b-b') ((Submodule.quotientRel_def _).mp hb)
      rw [M.cycleMul_sub_left] at h₁
      rw [M.cycleMul_sub_right] at h₂
      have he := Submodule.add_mem _ h₁ h₂
      convert he using 1
      abel)

/-- 余鎖積をコホモロジーへ降ろす。 -/
def onHomology {i j : ℕ} (x : K.homology i) (y : K.homology j) : K.homology (i + j) :=
  (K.sc (i + j)).moduleCatHomologyIso.inv
    (M.quotientMul ((K.sc i).moduleCatHomologyIso.hom x) ((K.sc j).moduleCatHomologyIso.hom y))

end CochainProduct

end SerrePositivity.HomologicalAlgebra
