module

public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.Naturality

/-!
# 非正次数テンソルの有限成分への射影

概要：Berger–Fresse §1.1 の整数模型で自然数鎖の有限成分 API を使う。
方針：負次数の直和比較の逆を通して自然数鎖の射影を移す。
規約：各非正全次数に非零となる次数分割は有限個。
使われ方：整数 AW 対角を切断公式で評価し、法則を成分で検証する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.NegativeTensor

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable {A : Type u} [CommRing A]

/-- 概要：延長した二複体のテンソルの負次数成分への射影（Berger–Fresse §1.1）。
方針：自然数テンソルに戻し有限成分の射影を移す。
規約：全次数 −n、二次数 −p,−q で p+q=n。
使われ方：AW 対角の整数成分公式。 -/
def projection (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n p q : ℕ) (h : p + q = n) :
    (HomologicalComplex.tensorObj (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L)).X (-(n : ℤ)) ⟶
      (_root_.SerrePositivity.NegativeTensor.extend K).X (-(p : ℤ)) ⊗ (_root_.SerrePositivity.NegativeTensor.extend L).X (-(q : ℤ)) :=
  _root_.SerrePositivity.NegativeTensor.degreeInv K L n ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L n p q h ≫
    ((_root_.SerrePositivity.NegativeTensor.xIso K p).inv ⊗ₘ (_root_.SerrePositivity.NegativeTensor.xIso L q).inv)

/-- 概要：比較の順方向の後の射影は元の有限射影（Berger–Fresse §1.1）。
方針：次数比較の順方向と逆方向を消す。
規約：出力因子は標準同型の逆で整数次数へ移す。
使われ方：整数 AW の成分を自然数 AW の成分へ帰着する。 -/
@[reassoc (attr := simp)]
lemma degreeMap_projection (K L : ChainComplex (ModuleCat.{u} A) ℕ)
    (n p q : ℕ) (h : p + q = n) :
    _root_.SerrePositivity.NegativeTensor.degreeMap K L n ≫ _root_.SerrePositivity.NegativeTensor.projection K L n p q h =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L n p q h ≫
        ((_root_.SerrePositivity.NegativeTensor.xIso K p).inv ⊗ₘ (_root_.SerrePositivity.NegativeTensor.xIso L q).inv) := by
  rw [_root_.SerrePositivity.NegativeTensor.projection, ← Category.assoc, ← Category.assoc, _root_.SerrePositivity.NegativeTensor.degreeMap_inv]
  simp

/-- 概要：負の全次数への射は全ての非正二次数への射影で決まる（Berger–Fresse §1.1）。
方針：次数比較と因子の同型を消し、自然数次数での外延性を使う。
規約：始域は任意の係数加群。
使われ方：整数 AW の射の法則を有限成分で検査する。 -/
lemma projection_hom_ext (K L : ChainComplex (ModuleCat.{u} A) ℕ)
    {N : ModuleCat.{u} A} {n : ℕ}
    {f g : N ⟶ (HomologicalComplex.tensorObj (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L)).X (-(n : ℤ))}
    (h : ∀ p q (hpq : p + q = n), f ≫ _root_.SerrePositivity.NegativeTensor.projection K L n p q hpq =
      g ≫ _root_.SerrePositivity.NegativeTensor.projection K L n p q hpq) : f = g := by
  apply (cancel_mono (_root_.SerrePositivity.NegativeTensor.degreeIso K L n).inv).1
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection_hom_ext
  intro p q hpq
  apply (cancel_mono ((_root_.SerrePositivity.NegativeTensor.xIso K p).inv ⊗ₘ (_root_.SerrePositivity.NegativeTensor.xIso L q).inv)).1
  simpa only [_root_.SerrePositivity.NegativeTensor.projection, _root_.SerrePositivity.NegativeTensor.degreeIso, Category.assoc] using h p q hpq

end SerrePositivity.NegativeTensor
