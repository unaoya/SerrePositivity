module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Field.Rat

/-!
# 全次数の Mayer–Vietoris 列と比較の五項補題

## 概要
`B_(n+1) → C_(n+1) → A_n → B_n → C_n` の全整数次数の完全列を保持する。
B と C の比較が全次数で同型なら A の指定比較も同型になる。

## 方針
境界写像とその自然性を明示し、Mathlib の加群の五項補題を各整数次数に適用する。

## 規約
実際のホモトピー引き戻しからの長完全列に適用する代数的な部品。
この列のデータを与えるだけで、任意の正方形がホモトピー引き戻しであるとは主張しない。

## 使われ方
論文 補題 3.3 の閉和、定理 3.1 の軌道正方形と (3.8) に対する全次数の帰納。
-/

@[expose] public section

universe u

open CategoryTheory

namespace SerrePositivity.KST.Descent

/-- 概要：全整数次数の Mayer–Vietoris 型の完全列（論文 §3）。
方針：三種類の次数付き群、二つの制限写像、次数を下げる境界写像を保持する。
規約：境界 `n` は `C_(n+1) → A_n`。自然数への切り捨てはしない。
使われ方：抽象 blowup の実降下から得る長完全列の π_* 側。 -/
structure GradedMayerVietoris where
  /-- 概要：元のスキームの値（論文 §3）。
  方針：全整数次数の有理加群を保持する。
  規約：負次数を含む。
  使われ方：帰納で同型性を示す項。 -/
  A : ℤ → ModuleCat.{u} ℚ
  /-- 概要：二つの被覆部分の値の積に相当する項（論文 §3）。
  方針：全整数次数の有理加群を保持する。
  規約：この抽象列では積との同定を別に供給する。
  使われ方：閉和・軌道正方形の比較。 -/
  B : ℤ → ModuleCat.{u} ℚ
  /-- 概要：交わりまたは例外部分の値（論文 §3）。
  方針：全整数次数の有理加群を保持する。
  規約：境界の始域となる。
  使われ方：中心上の帰納仮定。 -/
  C : ℤ → ModuleCat.{u} ℚ
  /-- 概要：被覆部分への制限（論文 §3）。
  方針：各次数の線形写像を記録する。
  規約：幾何学的な指定写像との同定を別に供給する。
  使われ方：Mayer–Vietoris 列の第一の射。 -/
  restriction : ∀ n, A n →ₗ[ℚ] B n
  /-- 概要：交わり上の制限の差（論文 §3）。
  方針：各次数の線形写像を記録する。
  規約：符号は具体的な正方形で固定する。
  使われ方：Mayer–Vietoris 列の第二の射。 -/
  difference : ∀ n, B n →ₗ[ℚ] C n
  /-- 概要：次数を一つ下げる境界（論文 §3 の抽象 blowup 降下）。
  方針：`C_(n+1) → A_n` と添字付けする。
  規約：境界が零であるとの仮定はしない。
  使われ方：次数ごとの通常の pullback では失われる情報を保持する。 -/
  boundary : ∀ n, C (n + 1) →ₗ[ℚ] A n
  /-- 概要：A_n における完全性（論文 §3）。
  方針：境界の像が制限の核に一致することを要求する。
  規約：実際の完全列を記述する構造の法則。
  使われ方：比較の五項補題。 -/
  exact_boundary_restriction : ∀ n, Function.Exact (boundary n) (restriction n)
  /-- 概要：B_n における完全性（論文 §3）。
  方針：制限の像が差の核に一致することを要求する。
  規約：制限の単射性は要求しない。
  使われ方：閉和・軌道正方形の貼り合わせ。 -/
  exact_restriction_difference : ∀ n, Function.Exact (restriction n) (difference n)
  /-- 概要：C_(n+1) における完全性（論文 §3）。
  方針：制限の差の像が境界の核に一致することを要求する。
  規約：境界を落とした通常の等化子条件には弱めない。
  使われ方：全次数の比較の五項補題。 -/
  exact_difference_boundary : ∀ n, Function.Exact (difference (n + 1)) (boundary n)

namespace GradedMayerVietoris

/-- 概要：全次数の完全列の比較（論文 補題 3.3・定理 3.1）。
方針：三項の次数ごとの写像と、境界を含む三つの可換式を保持する。
規約：単に三項の群が抽象的に同型というデータではない。
使われ方：幾何的な引き戻しや有理固定点による比較。 -/
structure Hom (S T : GradedMayerVietoris.{u}) where
  /-- 概要：元のスキームの比較（論文 §3）。
  方針：次数ごとの指定線形写像を保持する。
  規約：同型性はこのデータには含めない。
  使われ方：五項補題の結論。 -/
  mapA : ∀ n, S.A n →ₗ[ℚ] T.A n
  /-- 概要：二つの部分の比較（論文 §3）。
  方針：次数ごとの指定線形写像を保持する。
  規約：同型性は定理の仮定で別に与える。
  使われ方：五項補題の既知の辺。 -/
  mapB : ∀ n, S.B n →ₗ[ℚ] T.B n
  /-- 概要：交わりの比較（論文 §3）。
  方針：次数ごとの指定線形写像を保持する。
  規約：同型性は定理の仮定で別に与える。
  使われ方：中心上の帰納仮定。 -/
  mapC : ∀ n, S.C n →ₗ[ℚ] T.C n
  /-- 概要：制限との可換性（論文 §3）。
  方針：比較が制限の指定写像と両立することを記録する。
  規約：すべての整数次数で要求する。
  使われ方：五項補題の可換正方形。 -/
  comm_restriction : ∀ n, (T.restriction n).comp (mapA n) =
    (mapB n).comp (S.restriction n)
  /-- 概要：制限の差との可換性（論文 §3）。
  方針：比較が差の指定写像と両立することを記録する。
  規約：符号もこの式に含まれる。
  使われ方：五項補題の可換正方形。 -/
  comm_difference : ∀ n, (T.difference n).comp (mapB n) =
    (mapC n).comp (S.difference n)
  /-- 概要：境界写像の自然性（論文 §3）。
  方針：隣接する二つの次数を結ぶ比較の可換性を要求する。
  規約：次数ごとの群の同型から自動では得られない情報。
  使われ方：五項補題と全次数の帰納。 -/
  comm_boundary : ∀ n, (T.boundary n).comp (mapC (n + 1)) =
    (mapA n).comp (S.boundary n)

/-- 概要：部分と交わりの比較が全次数同型なら元の比較も全次数同型（論文 §3）。
方針：`B_(n+1) → C_(n+1) → A_n → B_n → C_n` に加群の五項補題を適用する。
規約：指定写像の全単射性を結論し、境界の自然性を明示的に使用する。
使われ方：補題 3.3 の閉和と定理 3.1 の軌道正方形の帰納。 -/
theorem Hom.bijective_mapA {S T : GradedMayerVietoris.{u}} (f : Hom S T)
    (hB : ∀ n, Function.Bijective (f.mapB n)) (hC : ∀ n, Function.Bijective (f.mapC n))
    (n : ℤ) : Function.Bijective (f.mapA n) :=
  LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (S.difference (n + 1)) (S.boundary n) (S.restriction n) (S.difference n)
    (T.difference (n + 1)) (T.boundary n) (T.restriction n) (T.difference n)
    (f.mapB (n + 1)) (f.mapC (n + 1)) (f.mapA n) (f.mapB n) (f.mapC n)
    (f.comm_difference (n + 1)) (f.comm_boundary n) (f.comm_restriction n)
    (f.comm_difference n)
    (S.exact_difference_boundary n) (S.exact_boundary_restriction n)
    (S.exact_restriction_difference n)
    (T.exact_difference_boundary n) (T.exact_boundary_restriction n)
    (T.exact_restriction_difference n)
    (hB (n + 1)).2 (hC (n + 1)) (hB n) (hC n).1

end GradedMayerVietoris

end SerrePositivity.KST.Descent
