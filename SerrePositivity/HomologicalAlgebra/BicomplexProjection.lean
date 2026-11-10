module

public import Mathlib.Algebra.Homology.TotalComplex

/-!
# 第一象限双複体の軸への射影

## 概要
自然数で二重に添字付けた余鎖双複体の総複体から第 0 行と第 0 列へ射影する。

## 方針
総複体の余積表示で、対象の軸上の成分を恒等射、それ以外を零にする。

## 規約
横の微分に符号を加えず、縦の微分は横次数による符号を持つ。

## 使われ方
pd de Rham 双複体の比較射。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomologicalAlgebra

variable {C : Type*} [Category* C] [Preadditive C]

local notation "up" => ComplexShape.up ℕ

/-- 第一象限の総複体に用いる通常の横・縦の符号。 -/
instance cochainNatTensorSigns : ComplexShape.TensorSigns up where
  ε' := MonoidHom.mk' (fun n => (-1 : ℤˣ) ^ n.toAdd) (fun a b => pow_add _ a.toAdd b.toAdd)
  rel_add p q r (hpq : p + 1 = q) := by change p + r + 1 = q + r; omega
  add_rel p q r (hpq : p + 1 = q) := by change r + p + 1 = r + q; omega
  ε'_succ := by
    rintro p _ rfl
    change (-1 : ℤˣ) ^ (p+1) = -((-1 : ℤˣ) ^ p)
    rw [pow_succ, mul_neg, mul_one]

variable (K : HomologicalComplex₂ C up up) [K.HasTotal up]

/-- 双複体の横方向を固定した行。 -/
abbrev bicomplexRow (j : ℕ) : CochainComplex C ℕ where
  X i := (K.X i).X j
  d a b := (K.d a b).f j
  shape a b h := by rw [K.shape a b h]; rfl
  d_comp_d' a b c hab hbc := by
    exact congrArg (fun f : K.X a ⟶ K.X c => f.f j) (K.d_comp_d a b c)

private def rowZeroApp (n : ℕ) : (K.total up).X n ⟶ (bicomplexRow K 0).X n :=
  K.totalDesc (fun a b h => if hb : b = 0 then
    eqToHom (by
      change a + b = n at h
      subst b
      rw [Nat.add_zero] at h
      subst n
      rfl)
    else 0)

private def columnZeroApp (n : ℕ) : (K.total up).X n ⟶ (K.X 0).X n :=
  K.totalDesc (fun a b h => if ha : a = 0 then
    eqToHom (by
      change a + b = n at h
      subst a
      rw [Nat.zero_add] at h
      subst n
      rfl)
    else 0)

private theorem total_d_summand (a b n : ℕ)
    (h : ComplexShape.π up up up (a,b) = n) :
    K.ιTotal up a b n h ≫ (K.total up).d n (n+1) =
      (K.d a (a+1)).f b ≫ K.ιTotal up (a+1) b (n+1) (by
        change a + b = n at h
        change (a + 1) + b = n+1
        omega) +
      (-1 : ℤ)^a • ((K.X a).d b (b+1) ≫ K.ιTotal up a (b+1) (n+1) (by
        change a + b = n at h
        change a + (b+1) = n+1
        omega)) := by
  change K.ιTotal up a b n h ≫ (K.D₁ up n (n+1) + K.D₂ up n (n+1)) = _
  rw [Preadditive.comp_add, K.ι_D₁, K.ι_D₂]
  rw [K.d₁_eq up (i₁' := a+1) rfl b (n+1) (by change a+b = n at h; change (a+1)+b=n+1; omega),
    K.d₂_eq up a (i₂' := b+1) rfl (n+1) (by change a+b=n at h; change a+(b+1)=n+1; omega)]
  change (1 : ℤ) • ((K.d a (a+1)).f b ≫ K.ιTotal up (a+1) b (n+1) _) +
    (↑((-1 : ℤˣ)^a) : ℤ) • ((K.X a).d b (b+1) ≫ K.ιTotal up a (b+1) (n+1) _) = _
  rw [one_smul, Units.val_pow_eq_pow_val]
  rfl

/-- 総複体から第 0 行への余鎖写像。 -/
def totalToRowZero : K.total up ⟶ bicomplexRow K 0 where
  f := rowZeroApp K
  comm' n m hnm := by
    have h : n+1 = m := hnm
    subst m
    apply HomologicalComplex₂.total.hom_ext
    intro a b h
    rw [← Category.assoc, ← Category.assoc, total_d_summand,
      Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc, Category.assoc]
    by_cases hb : b = 0
    · change a + b = n at h
      subst b
      simp only [Nat.add_zero] at h
      subst n
      simp [rowZeroApp, bicomplexRow]
    · simp [rowZeroApp, hb]

/-- 総複体から第 0 列への余鎖写像。 -/
def totalToColumnZero : K.total up ⟶ K.X 0 where
  f := columnZeroApp K
  comm' n m hnm := by
    have h : n+1 = m := hnm
    subst m
    apply HomologicalComplex₂.total.hom_ext
    intro a b h
    rw [← Category.assoc, ← Category.assoc, total_d_summand,
      Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc, Category.assoc]
    by_cases ha : a = 0
    · subst a
      have hbn : b = n := (Nat.zero_add b).symm.trans h
      subst n
      simp [columnZeroApp]
    · simp [columnZeroApp, ha]

end SerrePositivity.HomologicalAlgebra
