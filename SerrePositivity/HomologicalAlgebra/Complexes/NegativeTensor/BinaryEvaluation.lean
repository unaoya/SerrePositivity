module

public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.BinaryMap

/-!
# 負次数へ移した二入力写像の評価

概要：Berger–Fresse §1.1.3 の正規化生成元の公式を整数模型で使う。
方針：標準テンソル比較の順方向と逆方向を消し、斉次包含で評価する。
規約：p+q=n の任意の自然数全次数の同定を許す。
使われ方：一般 shuffle と既存 BE 部分合成の一致。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.NegativeTensor

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped _root_.TensorProduct

variable {A : Type u} [CommRing A]

/-- 概要：二入力写像の移送を比較の順方向で戻す（BF §1.1.3）。
方針：比較同型とその逆を消す。
規約：任意の二入力の鎖写像を扱う。
使われ方：移送した写像の生成元公式を導く。 -/
@[reassoc (attr := simp)]
lemma comparison_binaryMap {K L M : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : _root_.SerrePositivity.NatTensor.tensor K L ⟶ M) :
    (_root_.SerrePositivity.NegativeTensor.comparison K L).hom ≫ _root_.SerrePositivity.NegativeTensor.binaryMap f = extendMap f ComplexShape.embeddingDownNat := by
  simp only [_root_.SerrePositivity.NegativeTensor.binaryMap, Iso.hom_inv_id_assoc]

/-- 概要：移送した二入力写像の負次数の純テンソル上の値（BF §1.1.3）。
方針：比較の順方向を消す等式を自然数鎖の斉次包含で評価する。
規約：因子の次数は −p,−q、全次数は −n。
使われ方：一般 shuffle の整数生成元公式。 -/
lemma binaryMap_neg_tmul {K L M : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : _root_.SerrePositivity.NatTensor.tensor K L ⟶ M) (p q n : ℕ) (h : p + q = n) (x : K.X p) (y : L.X q) :
    (_root_.SerrePositivity.NegativeTensor.binaryMap f).f (-(n : ℤ))
        (ιTensorObj (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (by omega)
          ((_root_.SerrePositivity.NegativeTensor.xIso K p).inv x ⊗ₜ[A] (_root_.SerrePositivity.NegativeTensor.xIso L q).inv y)) =
      (_root_.SerrePositivity.NegativeTensor.xIso M n).inv (f.f n (ιTensorObj K L p q n h (x ⊗ₜ[A] y))) := by
  have hv := congrArg (fun g => g.f (-(n : ℤ))
    ((_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.NatTensor.tensor K L) n).inv (ιTensorObj K L p q n h (x ⊗ₜ[A] y))))
      (_root_.SerrePositivity.NegativeTensor.comparison_binaryMap f)
  change (_root_.SerrePositivity.NegativeTensor.binaryMap f).f (-(n : ℤ))
      ((_root_.SerrePositivity.NegativeTensor.comparison K L).hom.f (-(n : ℤ))
        ((_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.NatTensor.tensor K L) n).inv (ιTensorObj K L p q n h (x ⊗ₜ[A] y)))) = _ at hv
  rw [_root_.SerrePositivity.NegativeTensor.comparison_neg_inv_apply, _root_.SerrePositivity.NegativeTensor.degreeMap_ι_tmul, _root_.SerrePositivity.NegativeTensor.extendMap_neg_inv_apply] at hv
  exact hv

end SerrePositivity.NegativeTensor
