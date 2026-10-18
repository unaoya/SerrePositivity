module

public import SerrePositivity.KST.Descent.Axioms
public import SerrePositivity.KST.Descent.MayerVietoris
public import Mathlib.CategoryTheory.Square
public import Mathlib.LinearAlgebra.Prod

/-!
# 前層の正方形の制限写像と全次数の長完全列

## 概要
可換正方形に前層を適用し、二つの部分への制限と、交わりでの制限の差を指定する。
境界を含む長完全列のデータを、全次数の Mayer–Vietoris 比較に結び付ける。

## 方針
二つの制限写像は前層の引き戻しから構成する。境界と完全性は実降下から供給するデータ。

## 規約
任意の可換正方形が降下を満たすとは主張しない。
境界の存在と自然性は通常の群の pullback や関手性だけでは得られない。

## 使われ方
論文 補題 3.3 の閉和と定理 3.1 の軌道正方形に対する公理 (2) の π_* 側。
-/

@[expose] public section

universe u v w t

open CategoryTheory Opposite

namespace SerrePositivity.KST.Descent

namespace GradedPresheaf

variable {C : Type u} [Category.{v} C] {Coefficient : Type w}
variable (L : GradedPresheaf.{u, v, w, t} C Coefficient)

/-- 概要：正方形の右下から右上・左下への制限（論文 §3）。
方針：前層の二つの引き戻しの積を取る。
規約：両成分とも正の符号。
使われ方：抽象 blowup 正方形の Mayer–Vietoris 列の第一の射。 -/
def squareRestriction (H : Coefficient) (n : ℤ) (sq : Square C) :
    (L H n).obj (op sq.X₄) →ₗ[ℚ]
      (L H n).obj (op sq.X₂) × (L H n).obj (op sq.X₃) :=
  (L.pullback H n sq.f₂₄).prod (L.pullback H n sq.f₃₄)

/-- 概要：右上・左下から左上への制限の差（論文 §3）。
方針：上辺の引き戻しから左辺の引き戻しを引く。
規約：符号は上辺が正、左辺が負。
使われ方：閉和・軌道正方形の Mayer–Vietoris 列の第二の射。 -/
def squareDifference (H : Coefficient) (n : ℤ) (sq : Square C) :
    ((L H n).obj (op sq.X₂) × (L H n).obj (op sq.X₃)) →ₗ[ℚ]
      (L H n).obj (op sq.X₁) :=
  (L.pullback H n sq.f₁₂).comp (LinearMap.fst ℚ _ _) -
    (L.pullback H n sq.f₁₃).comp (LinearMap.snd ℚ _ _)

/-- 概要：正方形の二つの制限写像の合成は零（論文 §3）。
方針：反変合成と正方形の可換式を使う。
規約：この零合成だけでは完全性や実降下は結論しない。
使われ方：指定制限写像と Mayer–Vietoris 列の整合性。 -/
theorem squareDifference_comp_squareRestriction (H : Coefficient) (n : ℤ) (sq : Square C) :
    (L.squareDifference H n sq).comp (L.squareRestriction H n sq) = 0 := by
  ext x
  change L.pullback H n sq.f₁₂ (L.pullback H n sq.f₂₄ x) -
    L.pullback H n sq.f₁₃ (L.pullback H n sq.f₃₄ x) = 0
  rw [sub_eq_zero]
  have h := congrArg (fun f ↦ L.pullback H n f x) sq.fac
  simpa only [pullback_comp, LinearMap.comp_apply] using h

/-- 概要：自然変換は指定引き戻しと可換（論文 (3.7) の比較）。
方針：自然性の式を元で評価する。
規約：元の比較写像と両立する向きで述べる。
使われ方：Mayer–Vietoris 比較の制限と差の可換性。 -/
theorem natTrans_pullback {M : GradedPresheaf.{u, v, w, t} C Coefficient}
    (H : Coefficient) (n : ℤ) (e : L H n ⟶ M H n)
    {X Y : C} (f : X ⟶ Y) (x : (L H n).obj (op Y)) :
    M.pullback H n f ((e.app (op Y)).hom x) =
      (e.app (op X)).hom (L.pullback H n f x) := by
  exact (congrArg (fun k ↦ k.hom x) (e.naturality f.op)).symm

end GradedPresheaf

/-- 概要：前層の指定制限を持つ正方形の長完全列（論文 §3）。
方針：境界写像と三箇所の完全性を保持し、二つの制限は前層の写像そのものを使う。
規約：公理 (2) の実降下からこのデータを供給する必要がある。
データの存在だけをホモトピー引き戻し性の定義としては使わない。
使われ方：閉和・軌道正方形の全次数の比較。 -/
structure SquareMayerVietoris {C : Type u} [Category.{v} C] {Coefficient : Type w}
    (L : GradedPresheaf.{u, v, w, t} C Coefficient) (H : Coefficient) (sq : Square C) where
  /-- 概要：実降下からの次数を下げる境界（論文 §3）。
  方針：左上の次数 n+1 から右下の次数 n への写像を保持する。
  規約：前層の関手性だけから存在すると仮定しない。
  使われ方：正方形の長完全列。 -/
  boundary : ∀ n, (L H (n + 1)).obj (op sq.X₁) →ₗ[ℚ] (L H n).obj (op sq.X₄)
  /-- 概要：元のスキームの値での完全性（論文 §3）。
  方針：境界の像と制限の核の一致を保持する。
  規約：すべての整数次数を含む。
  使われ方：比較の五項補題。 -/
  exact_boundary_restriction : ∀ n, Function.Exact (boundary n) (L.squareRestriction H n sq)
  /-- 概要：二つの部分の値の積での完全性（論文 §3）。
  方針：制限の像と制限の差の核の一致を保持する。
  規約：指定した符号を用いる。
  使われ方：閉和の貼り合わせ。 -/
  exact_restriction_difference : ∀ n,
    Function.Exact (L.squareRestriction H n sq) (L.squareDifference H n sq)
  /-- 概要：交わりの値での完全性（論文 §3）。
  方針：制限の差の像と境界の核の一致を保持する。
  規約：境界の自然性は列の比較で別に要求する。
  使われ方：中心上の帰納から元のスキームへの比較。 -/
  exact_difference_boundary : ∀ n,
    Function.Exact (L.squareDifference H (n + 1) sq) (boundary n)

namespace SquareMayerVietoris

variable {C : Type u} [Category.{v} C] {Coefficient : Type w}
variable {L M : GradedPresheaf.{u, v, w, t} C Coefficient} {H : Coefficient} {sq : Square C}

/-- 概要：正方形の指定された長完全列を共通の全次数列へ移す（論文 §3）。
方針：右下、右上と左下の積、左上をそれぞれ A、B、C とする。
規約：元の制限写像と境界を変えない。
使われ方：境界の自然性を含む五項補題の適用。 -/
def toGraded (S : SquareMayerVietoris L H sq) : GradedMayerVietoris.{t} where
  A n := (L H n).obj (op sq.X₄)
  B n := ModuleCat.of ℚ ((L H n).obj (op sq.X₂) × (L H n).obj (op sq.X₃))
  C n := (L H n).obj (op sq.X₁)
  restriction n := L.squareRestriction H n sq
  difference n := L.squareDifference H n sq
  boundary := S.boundary
  exact_boundary_restriction := S.exact_boundary_restriction
  exact_restriction_difference := S.exact_restriction_difference
  exact_difference_boundary := S.exact_difference_boundary

/-- 概要：前層の自然な比較を境界と両立する長完全列の比較へ移す（論文 §3）。
方針：制限と差の可換性は自然性から証明し、境界の可換性だけを入力する。
規約：境界の自然性を次数ごとの群の同型から推論しない。
使われ方：二つの降下前層や固定点比較の五項補題。 -/
def comparison (S : SquareMayerVietoris L H sq) (T : SquareMayerVietoris M H sq)
    (e : ∀ n, L H n ⟶ M H n)
    (boundary_naturality : ∀ n, (T.boundary n).comp ((e (n + 1)).app (op sq.X₁)).hom =
      ((e n).app (op sq.X₄)).hom.comp (S.boundary n)) :
    GradedMayerVietoris.Hom S.toGraded T.toGraded where
  mapA n := ((e n).app (op sq.X₄)).hom
  mapB n := (((e n).app (op sq.X₂)).hom).prodMap (((e n).app (op sq.X₃)).hom)
  mapC n := ((e n).app (op sq.X₁)).hom
  comm_restriction n := by
    ext x
    apply Prod.ext
    · exact L.natTrans_pullback H n (e n) sq.f₂₄ x
    · exact L.natTrans_pullback H n (e n) sq.f₃₄ x
  comm_difference n := by
    ext x
    change M.pullback H n sq.f₁₂ (((e n).app (op sq.X₂)).hom x.1) -
      M.pullback H n sq.f₁₃ (((e n).app (op sq.X₃)).hom x.2) =
      ((e n).app (op sq.X₁)).hom
        (L.pullback H n sq.f₁₂ x.1 - L.pullback H n sq.f₁₃ x.2)
    rw [L.natTrans_pullback, L.natTrans_pullback, map_sub]
  comm_boundary := boundary_naturality

/-- 概要：正方形の三つの部分での比較から右下の指定比較の同型を得る（論文 §3）。
方針：積の比較の全単射性を二成分から示し、境界と両立する五項補題を適用する。
規約：三つの部分について全整数次数で仮定し、境界の自然性も明示する。
使われ方：補題 3.3 の閉和と定理 3.1 の軌道正方形の帰納。 -/
theorem bijective_base_of_three_vertices
    (S : SquareMayerVietoris L H sq) (T : SquareMayerVietoris M H sq)
    (e : ∀ n, L H n ⟶ M H n)
    (boundary_naturality : ∀ n, (T.boundary n).comp ((e (n + 1)).app (op sq.X₁)).hom =
      ((e n).app (op sq.X₄)).hom.comp (S.boundary n))
    (h₂ : ∀ n, Function.Bijective (((e n).app (op sq.X₂)).hom))
    (h₃ : ∀ n, Function.Bijective (((e n).app (op sq.X₃)).hom))
    (h₁ : ∀ n, Function.Bijective (((e n).app (op sq.X₁)).hom)) (n : ℤ) :
    Function.Bijective (((e n).app (op sq.X₄)).hom) := by
  apply (S.comparison T e boundary_naturality).bijective_mapA ?_ h₁ n
  intro k
  constructor
  · intro x y h
    exact Prod.ext ((h₂ k).1 (congrArg Prod.fst h)) ((h₃ k).1 (congrArg Prod.snd h))
  · rintro ⟨x, y⟩
    obtain ⟨x', hx⟩ := (h₂ k).2 x
    obtain ⟨y', hy⟩ := (h₃ k).2 y
    exact ⟨(x', y'), Prod.ext hx hy⟩

end SquareMayerVietoris

end SerrePositivity.KST.Descent
