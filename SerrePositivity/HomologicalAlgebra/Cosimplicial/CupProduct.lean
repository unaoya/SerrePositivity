module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Cohomology

/-!
# 余単体的可換環の Alexander–Whitney 積

## 概要
前面と後面への構造射から、余鎖上の Alexander–Whitney 積を作る。

## 方針
結合律と単位律は単体圏の写像の合成で確認する。

## 規約
二つの面は境界の一頂点を共有する。

## 使われ方
Hodge–Tate 写像の積と pd de Rham 双複体の積。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SerrePositivity.Cosimplicial

/-- 概要：前面 [m] → [m+n]、i ↦ i。
方針：`SimplexCategory.mkHom` と単調写像。
規約：—
使われ方：cup 積の第一因子の引き戻し。 -/
def frontFace (m n : ℕ) : (⦋m⦌ : SimplexCategory) ⟶ ⦋m + n⦌ :=
  SimplexCategory.mkHom ⟨fun i => ⟨i, by omega⟩, fun _ _ h => h⟩

/-- 概要：後面 [n] → [m+n]、i ↦ m + i。
方針：同上。
規約：—
使われ方：cup 積の第二因子の引き戻し。 -/
def backFace (m n : ℕ) : (⦋n⦌ : SimplexCategory) ⟶ ⦋m + n⦌ :=
  SimplexCategory.mkHom ⟨fun i => ⟨m + i, by omega⟩, fun _ _ h => by simpa using h⟩

variable (X : CosimplicialObject CommRingCat.{u})

private theorem cast_obj {a b : ℕ} (h : a = b) (x : X.obj ⦋a⦌) :
    cast (congrArg (fun n => (X.obj ⦋n⦌ : Type u)) h) x =
      X.map (eqToHom (congrArg SimplexCategory.mk h)) x := by
  subst b
  simp

/-- 概要：cup 積 X^m × X^n → X^{m+n}、x ∪ y := (frontFace)^*(x) · (backFace)^*(y)。
方針：Alexander–Whitney。
規約：双線形。
使われ方：非正規化複体の dg 環構造。 -/
def cup {m n : ℕ} (x : X.obj ⦋m⦌) (y : X.obj ⦋n⦌) : X.obj ⦋m + n⦌ :=
  X.map (frontFace m n) x * X.map (backFace m n) y

/-- 概要：cup 積の結合律（鎖のレベルで成り立つ）。
方針：前面・後面の合成の余単体的恒等式と環の結合律。
規約：次数の和の結合は `Nat.add_assoc` で移す。
使われ方：dg 環。 -/
theorem cup_assoc {l m n : ℕ} (x : X.obj ⦋l⦌) (y : X.obj ⦋m⦌) (z : X.obj ⦋n⦌) :
    cast (by rw [Nat.add_assoc]) (cup X (cup X x y) z) = cup X x (cup X y z) := by
  let h : ⦋(l + m) + n⦌ = ⦋l + (m + n)⦌ := congrArg SimplexCategory.mk (Nat.add_assoc l m n)
  change cast (congrArg (fun i => (X.obj ⦋i⦌ : Type u)) (Nat.add_assoc l m n))
    (cup X (cup X x y) z) = _
  rw [cast_obj X (Nat.add_assoc l m n)]
  have hx : (frontFace l m ≫ frontFace (l + m) n) ≫ eqToHom h =
      frontFace l (m + n) := by
    ext i
    simp [frontFace]
    rfl
  have hy : (backFace l m ≫ frontFace (l + m) n) ≫ eqToHom h =
      frontFace m n ≫ backFace l (m + n) := by
    ext i
    simp [frontFace, backFace]
    rfl
  have hz : backFace (l + m) n ≫ eqToHom h =
      backFace m n ≫ backFace l (m + n) := by
    ext i
    simp [backFace, Nat.add_assoc]
    rfl
  simp only [cup, map_mul, ← CommRingCat.comp_apply, ← X.map_comp]
  rw [show eqToHom (congrArg SimplexCategory.mk (Nat.add_assoc l m n)) = eqToHom h from rfl]
  rw [hx, hy, hz, mul_assoc]

/-- 概要：単位元 1 ∈ X^0 は cup 積の単位。
方針：面写像は環射なので 1 を保つ。
規約：—
使われ方：dg 環。 -/
theorem one_cup {n : ℕ} (y : X.obj ⦋n⦌) : cast (by simp) (cup X (1 : X.obj ⦋0⦌) y) = y := by
  let h : ⦋0 + n⦌ = ⦋n⦌ := congrArg SimplexCategory.mk (Nat.zero_add n)
  change cast (congrArg (fun i => (X.obj ⦋i⦌ : Type u)) (Nat.zero_add n))
    (cup X (1 : X.obj ⦋0⦌) y) = _
  rw [cast_obj X (Nat.zero_add n)]
  have hy : backFace 0 n ≫ eqToHom h = 𝟙 ⦋n⦌ := by
    ext i
    simp [backFace]
  simp only [cup, map_one, one_mul, ← CommRingCat.comp_apply, ← X.map_comp]
  rw [show eqToHom (congrArg SimplexCategory.mk (Nat.zero_add n)) = eqToHom h from rfl, hy]
  simp

/-- 余単体的環の射は余鎖の cup 積を保つ。 -/
theorem cup_natural {Y : CosimplicialObject CommRingCat.{u}} (f : X ⟶ Y)
    {m n : ℕ} (x : X.obj ⦋m⦌) (y : X.obj ⦋n⦌) :
    f.app ⦋m + n⦌ (cup X x y) = cup Y (f.app ⦋m⦌ x) (f.app ⦋n⦌ y) := by
  simp only [cup, map_mul, ← CommRingCat.comp_apply, f.naturality]

/-- cup 積は左因子について加法的。 -/
theorem add_cup {m n : ℕ} (x x' : X.obj ⦋m⦌) (y : X.obj ⦋n⦌) :
    cup X (x + x') y = cup X x y + cup X x' y := by
  simp only [cup, map_add, add_mul]

/-- cup 積は右因子について加法的。 -/
theorem cup_add {m n : ℕ} (x : X.obj ⦋m⦌) (y y' : X.obj ⦋n⦌) :
    cup X x (y + y') = cup X x y + cup X x y' := by
  simp only [cup, map_add, mul_add]

end SerrePositivity.Cosimplicial
