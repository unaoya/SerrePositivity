module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Hadamard
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Commutative

/-!
模型。文献の定義との比較は後で
# Hopf dg オペラッド

概要：Berger–Fresse §1.1.4 の余単位付き Hopf オペラッドの界面を定義する。
方針：対角と余単位を実際のオペラッド射で持ち、各 arity で余代数則を要求する。
規約：余可換性は要求しない。AW 対角は厳密に余結合的である。
使われ方：E-coalgebra 区間と代数のテンソル・path object の入力となる。
-/

@[expose] public section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：余単位付き Hopf dg オペラッド構造（Berger–Fresse §1.1.4）。
方針：arity ごとの余代数則と、単位・部分合成を保つ対角・余単位を束ねる。
規約：arity 0 を含み、余可換性や cofibrancy は仮定しない。
使われ方：Hopf オペラッドに基づく代数のテンソルと区間転送に用いる。 -/
structure Hopf (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) where
  /-- 概要：Hopf 対角（BF §1.1.4）。
  方針：Hadamard 積へのオペラッド射とする。
  規約：単位と全ての部分合成を保存する。
  使われ方：二つの代数のテンソルに演算を分配する。 -/
  diagonal : P ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.hadamard P P
  /-- 概要：Hopf 余単位（BF §1.1.4）。
  方針：可換オペラッドへの射として持つ。
  規約：全 arity の終域はテンソル単位 A[0]。
  使われ方：テンソル代数の単位構造を供給する。 -/
  counit : P ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A
  /-- 概要：各 arity の余結合性（BF §1.1.4）。
  方針：結合子を介して二つの反復対角を比較する。
  規約：chain map 全体の等式である。
  使われ方：テンソル代数の結合子との両立を保証する。 -/
  coassoc (n : ℕ) :
    diagonal.map.app (_root_.SerrePositivity.FiniteBijection.of n) ≫
        (diagonal.map.app (_root_.SerrePositivity.FiniteBijection.of n) ▷ P.arity n) ≫
        (α_ (P.arity n) (P.arity n) (P.arity n)).hom =
      diagonal.map.app (_root_.SerrePositivity.FiniteBijection.of n) ≫
        (P.arity n ◁ diagonal.map.app (_root_.SerrePositivity.FiniteBijection.of n))
  /-- 概要：各 arity の左余単位則（BF §1.1.4）。
  方針：左因子に余単位を適用して単位子で消す。
  規約：元の演算の恒等射を得る。
  使われ方：テンソル代数の左単位則を保証する。 -/
  left_counit (n : ℕ) :
    diagonal.map.app (_root_.SerrePositivity.FiniteBijection.of n) ≫
        (counit.map.app (_root_.SerrePositivity.FiniteBijection.of n) ▷ P.arity n) ≫
        (λ_ (P.arity n)).hom = 𝟙 (P.arity n)
  /-- 概要：各 arity の右余単位則（BF §1.1.4）。
  方針：右因子に余単位を適用して単位子で消す。
  規約：元の演算の恒等射を得る。
  使われ方：テンソル代数の右単位則を保証する。 -/
  right_counit (n : ℕ) :
    diagonal.map.app (_root_.SerrePositivity.FiniteBijection.of n) ≫
        (P.arity n ◁ counit.map.app (_root_.SerrePositivity.FiniteBijection.of n)) ≫
        (ρ_ (P.arity n)).hom = 𝟙 (P.arity n)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
