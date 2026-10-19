module

public import SerrePositivity.EInfinity.NegativeTensor.Naturality

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

namespace SerrePositivity.EInfinity.NegativeTensor

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

variable {A : Type u} [CommRing A]

/-- 概要：延長した二複体のテンソルの負次数成分への射影（Berger–Fresse §1.1）。
方針：自然数テンソルに戻し有限成分の射影を移す。
規約：全次数 −n、二次数 −p,−q で p+q=n。
使われ方：AW 対角の整数成分公式。 -/
def projection (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n p q : ℕ) (h : p + q = n) :
    (HomologicalComplex.tensorObj (extend K) (extend L)).X (-(n : ℤ)) ⟶
      (extend K).X (-(p : ℤ)) ⊗ (extend L).X (-(q : ℤ)) :=
  degreeInv K L n ≫ AlexanderWhitney.tensorProjection K L n p q h ≫
    ((xIso K p).inv ⊗ₘ (xIso L q).inv)

/-- 概要：比較の順方向の後の射影は元の有限射影（Berger–Fresse §1.1）。
方針：次数比較の順方向と逆方向を消す。
規約：出力因子は標準同型の逆で整数次数へ移す。
使われ方：整数 AW の成分を自然数 AW の成分へ帰着する。 -/
@[reassoc (attr := simp)]
lemma degreeMap_projection (K L : ChainComplex (ModuleCat.{u} A) ℕ)
    (n p q : ℕ) (h : p + q = n) :
    degreeMap K L n ≫ projection K L n p q h =
      AlexanderWhitney.tensorProjection K L n p q h ≫
        ((xIso K p).inv ⊗ₘ (xIso L q).inv) := by
  rw [projection, ← Category.assoc, ← Category.assoc, degreeMap_inv]
  simp

/-- 概要：負の全次数への射は全ての非正二次数への射影で決まる（Berger–Fresse §1.1）。
方針：次数比較と因子の同型を消し、自然数次数での外延性を使う。
規約：始域は任意の係数加群。
使われ方：整数 AW の射の法則を有限成分で検査する。 -/
lemma projection_hom_ext (K L : ChainComplex (ModuleCat.{u} A) ℕ)
    {N : ModuleCat.{u} A} {n : ℕ}
    {f g : N ⟶ (HomologicalComplex.tensorObj (extend K) (extend L)).X (-(n : ℤ))}
    (h : ∀ p q (hpq : p + q = n), f ≫ projection K L n p q hpq =
      g ≫ projection K L n p q hpq) : f = g := by
  apply (cancel_mono (degreeIso K L n).inv).1
  apply AlexanderWhitney.tensorProjection_hom_ext
  intro p q hpq
  apply (cancel_mono ((xIso K p).inv ⊗ₘ (xIso L q).inv)).1
  simpa only [projection, degreeIso, Category.assoc] using h p q hpq

end SerrePositivity.EInfinity.NegativeTensor
