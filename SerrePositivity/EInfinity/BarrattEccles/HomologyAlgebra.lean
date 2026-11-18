module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyRing
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# E 代数の H⁰ は元のスカラー作用を持つ可換代数

概要：BF §1 の H⁰ の可換環構造を、基礎環 A 上の可換代数として束ねる。
方針：元のホモロジー加群のスカラー作用と積の双線形性を使う。
規約：新しいスカラー作用は選ばず、構造は局所的に使う。
使われ方：E2a-4 の H⁰ と E2b の通常の可換代数との比較。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

variable {A : Type u} [CommRing A]

/-- 概要：H⁰ の可換環構造は元の A 加群構造と両立（BF §1、BM §1）。
方針：二変数のスカラー線形性から Algebra.ofModule を適用する。
規約：元の homology 0 の Module A をそのまま使う。
使われ方：H⁰ を A 上の可換代数として扱う。 -/
@[instance_reducible]
def homologyAlgebra (X : (operad A).Algebra) :
    let := homologyCommRing X
    Algebra A (X.carrier.homology 0) := by
  let := homologyCommRing X
  exact Algebra.ofModule
    (_root_.SerrePositivity.HomologyZero.pairingValue_smul_left (homologyBinary X))
    (_root_.SerrePositivity.HomologyZero.pairingValue_smul_right (homologyBinary X))

/-- 概要：H⁰ の代数写像は実際の nullary の類のスカラー倍（BF §1）。
方針：元のスカラー作用を使った代数構造の単位を評価する。
規約：環と代数構造を局所的に選ぶ。
使われ方：離散可換代数との基礎環の比較。 -/
lemma homologyAlgebra_algebraMap (X : (operad A).Algebra) (a : A) :
    let := homologyCommRing X
    let := homologyAlgebra X
    algebraMap A (X.carrier.homology 0) a = a • homologyOne X := by
  let := homologyCommRing X
  let := homologyAlgebra X
  exact Algebra.algebraMap_eq_smul_one a

/-- 概要：E 代数の実際の H⁰ を通常の可換 A 代数として束ねる（BF §1）。
方針：構成済みの局所的な環・代数構造を付ける。
規約：底の型と加法・スカラー作用は元のホモロジー加群。
使われ方：E2b の離散対象とコホモロジーの界面。 -/
def homologyCommAlgebra (X : (operad A).Algebra) : CommAlgCat.{u} A := by
  let := homologyCommRing X
  let := homologyAlgebra X
  exact CommAlgCat.of A (X.carrier.homology 0)

end SerrePositivity.EInfinity.BarrattEccles
