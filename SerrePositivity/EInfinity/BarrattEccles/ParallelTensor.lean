module

public import SerrePositivity.EInfinity.BarrattEccles.TripleComplexExt
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
# 並列代入の二つの内側テンソル因子の交換

概要：Berger–Fresse §1.1.3 の並列代入で現れる三重テンソルの交換を計算する。
方針：結合子、内側の braiding、逆結合子を純粋斉次テンソルで評価する。
規約：第一因子を保ち、第二・第三因子を Koszul 符号付きで交換する。
使われ方：部分合成の並列結合則の右辺を成分で計算する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：逆結合子の二つの中間次数を独立に指定する（Berger–Fresse §1.1.3）。
方針：中間次数の等式を消去し、既存の純粋テンソルの公式を使う。
規約：右括弧の中間次数は l、左括弧の中間次数は m とする。
使われ方：入力を交換した後の次数を負の自然数の和に合わせる。 -/
lemma associator_inv_apply_of_sums (P Q T : Complex A) (i j k l m n : ℤ)
    (hl : j + k = l) (hm : i + j = m) (hn : i + l = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) :
    (α_ P Q T).inv.f n
        (ιTensorObj P (Q ⊗ T) i l n hn (x ⊗ₜ[A] ιTensorObj Q T j k l hl (y ⊗ₜ[A] z))) =
      ιTensorObj (P ⊗ Q) T m k n (by omega)
        (ιTensorObj P Q i j m hm (x ⊗ₜ[A] y) ⊗ₜ[A] z) := by
  subst l m
  exact SerrePositivity.DifferentialGraded.associator_inv_apply P Q T i j k (j + k) n rfl hn x y z

/-- 概要：三重テンソルの最後の二因子を交換する射（Berger–Fresse §1.1.3）。
方針：右括弧へ移し、内側を交換してから左括弧へ戻す。
規約：braiding は整数コチェイン複体の Koszul braiding である。
使われ方：オペラッドの並列結合則の交換部分を表す。 -/
def exchangeLastFactors (P Q T : Complex A) : (P ⊗ Q) ⊗ T ⟶ (P ⊗ T) ⊗ Q :=
  (α_ P Q T).hom ≫ (P ◁ (β_ Q T).hom) ≫ (α_ P T Q).inv

/-- 概要：最後の二因子の交換は次数の積の Koszul 符号を伴う（Berger–Fresse §1.1.3）。
方針：結合子と braiding の純粋斉次テンソルの公式を順に適用する。
規約：三つの中間次数は等しい整数の別名を許す。
使われ方：並列結合則の右辺を交換した shuffle 双線形写像へ帰着する。 -/
lemma exchangeLastFactors_apply (P Q T : Complex A) (i j k l m o n : ℤ)
    (hl : i + j = l) (hm : j + k = m) (ho : i + k = o) (hn : l + k = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) :
    (exchangeLastFactors P Q T).f n
        (ιTensorObj (P ⊗ Q) T l k n hn (ιTensorObj P Q i j l hl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
      (j * k).negOnePow • ιTensorObj (P ⊗ T) Q o j n (by omega)
        (ιTensorObj P T i k o ho (x ⊗ₜ[A] z) ⊗ₜ[A] y) := by
  simp only [exchangeLastFactors, HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [SerrePositivity.DifferentialGraded.associator_apply_of_sums P Q T i j k l m n hl hm hn,
    SerrePositivity.DifferentialGraded.whiskerLeft_apply P (β_ Q T).hom i m n (by omega)]
  rw [SerrePositivity.DifferentialGraded.braiding_eq_existing,
    SerrePositivity.DifferentialGraded.signedSwap_apply Q T j k m hm]
  rw [TensorProduct.tmul_smul]
  simp only [Units.smul_def, map_zsmul]
  rw [associator_inv_apply_of_sums P T Q i k j m o n (by omega) ho (by omega)]

/-- 概要：arity の等式のテンソルへの移送は右 whisker と一致する（Berger–Fresse §1.1.3）。
方針：arity の等式を消去し、恒等射の whisker の公式を使う。
規約：右の複体は固定する。
使われ方：並列結合則の中間 arity の移送を元で計算する。 -/
lemma arity_tensor_eqToHom (A : Type u) [CommRing A] {m n : ℕ} (h : m = n)
    (T : Complex A) :
    eqToHom (congrArg (fun q => complex A q ⊗ T) h) =
      eqToHom (congrArg (complex A) h) ▷ T := by
  cases h
  simp

end SerrePositivity.EInfinity.BarrattEccles
