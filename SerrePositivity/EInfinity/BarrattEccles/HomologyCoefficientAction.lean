module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyOperations
public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.PairingHomotopy

/-!
# E 代数の H⁰ の積は係数の切断の選択によらない

概要：BF §1 の E の可縮性から、augmentation が一である係数の選び替えを許す。
方針：係数の鎖ホモトピーを代数作用へ移し、H⁰ の双線形作用の等式を得る。
規約：対称群同変な切断は要求しない。
使われ方：H⁰ の積の可換性・結合性を、適切な係数射で計算する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：指定した arity 2 の係数を使う E 代数の二入力射（BF §1）。
方針：二入力テンソルを反復冪へ移して、単位からの係数射を作用へ入力する。
規約：係数の augmentation に条件を課さず定義する。
使われ方：H⁰ の積の選択独立性と可換性の比較。 -/
def coefficientBinary (X : (operad A).Algebra) (a : 𝟙_ (Complex A) ⟶ (operad A).arity 2) :
    X.carrier ⊗ X.carrier ⟶ X.carrier :=
  (X.carrier ◁ (oneIso X.carrier).inv) ≫ (λ_ (power X.carrier 2)).inv ≫
    (a ▷ power X.carrier 2) ≫ X.action 2

/-- 概要：係数のホモトピーは二入力作用のホモトピーを与える（BF §1）。
方針：係数ホモトピーを入力テンソルの恒等射とテンソルし、作用を合成する。
規約：実際の二入力複体射の鎖ホモトピー。
使われ方：H⁰ の作用から係数の違いを消す。 -/
def coefficientBinaryHomotopy (X : (operad A).Algebra)
    {a b : 𝟙_ (Complex A) ⟶ (operad A).arity 2} (h : Homotopy a b) :
    Homotopy (coefficientBinary X a) (coefficientBinary X b) := by
  have ht := SerrePositivity.cochainTensorHomotopyLeft h (𝟙 (power X.carrier 2))
  change Homotopy (a ⊗ₘ 𝟙 (power X.carrier 2)) (b ⊗ₘ 𝟙 (power X.carrier 2)) at ht
  simp only [tensorHom_id] at ht
  simpa only [coefficientBinary, Category.assoc] using
    (ht.compLeft ((X.carrier ◁ (oneIso X.carrier).inv) ≫
      (λ_ (power X.carrier 2)).inv)).compRight (X.action 2)

/-- 概要：同じ augmentation の二係数は同じ H⁰ の双線形作用を与える（BF §1）。
方針：E(2) の収縮から係数ホモトピーを作り、二入力作用へ移す。
規約：任意の可換基礎環、cofibrancy の仮定なし。
使われ方：環公理に適した係数の選択。 -/
lemma coefficientPairing_independent (X : (operad A).Algebra)
    (a b : 𝟙_ (Complex A) ⟶ (operad A).arity 2)
    (hab : a ≫ (augmentation A).map.app (FiniteBijection.of 2) =
      b ≫ (augmentation A).map.app (FiniteBijection.of 2)) :
    _root_.SerrePositivity.HomologyZero.pairing (coefficientBinary X a) =
      _root_.SerrePositivity.HomologyZero.pairing (coefficientBinary X b) :=
  _root_.SerrePositivity.HomologyZero.pairing_homotopy
    (coefficientBinaryHomotopy X (coefficientHomotopy A 2 a b hab))

/-- 概要：H⁰ の積は augmentation が一である任意の係数で計算できる（BF §1）。
方針：標準の収縮の切断と指定した係数の augmentation を比較する。
規約：同変な切断の存在を仮定しない。
使われ方：H⁰ の積の可換性と元の離散積との比較。 -/
lemma homologyProduct_eq_pairing (X : (operad A).Algebra)
    (a : 𝟙_ (Complex A) ⟶ (operad A).arity 2)
    (ha : a ≫ (augmentation A).map.app (FiniteBijection.of 2) = 𝟙 _) :
    homologyProduct X = _root_.SerrePositivity.HomologyZero.pairing (coefficientBinary X a) :=
  coefficientPairing_independent X (aritySection A 2) a
    ((aritySection_augmentation A 2).trans ha.symm)

end SerrePositivity.EInfinity.BarrattEccles
