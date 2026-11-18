module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyPermutation

/-!
# E 代数の実際の H⁰ の積の可換性

概要：BF §1 の E 代数の H⁰ の積は可換である。
方針：鎖レベルの交換ホモトピーを H⁰ の等式へ移す。
規約：元の homology 0 の加群上の、構成済みの積について述べる。
使われ方：E2a-4 の H⁰ の可換環構造。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory

variable {A : Type u} [CommRing A]

/-- 概要：E 代数の実際の H⁰ の積は可換（BF §1）。
方針：交換ホモトピーの H⁰ 作用の一致と、交換の作用の公式を合成する。
規約：任意の可換基礎環、特性零の仮定なし。
使われ方：H⁰ の可換環構造と単位則の左右比較。 -/
lemma homologyProduct_comm (X : (operad A).Algebra) (x y : X.carrier.homology 0) :
    homologyProduct X x y = homologyProduct X y x :=
  (congrArg (fun f => f x y)
    (_root_.SerrePositivity.HomologyZero.pairing_homotopy (homologyBinaryCommutativityHomotopy X))).trans
      (_root_.SerrePositivity.HomologyZero.pairing_braiding (homologyBinary X) x y)

end SerrePositivity.EInfinity.BarrattEccles
