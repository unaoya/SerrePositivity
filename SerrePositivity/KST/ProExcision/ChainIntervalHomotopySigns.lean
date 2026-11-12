module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ChainTensorHomotopy
public import Mathlib.Tactic.Abel

/-!
# 鎖区間評価のホモトピーの符号

概要：辺上で (−1)^(p+1)H_p と評価する符号を鎖ホモトピー等式から導く。
方針：零次と正次数でホモトピー等式を展開し、加法群の等式を整理する。
規約：KST Definition A.3、Construction A.5、辺の境界は終点−始点。
使われ方：全テンソル区間の区間次数1の微分可換性。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex
variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {K L : ChainComplex A ℕ} {f g : K ⟶ L} (H : Homotopy f g)

/-- 概要：零次の辺の評価の微分は終点写像から始点写像を引いたもの。
方針：零次の鎖ホモトピー等式を反転する。
規約：KST A.3・A.5、辺上の符号は (−1)^1。
使われ方：第一因子の零次の鎖区間条件。 -/
lemma chainIntervalHomotopySign_zero :
    (-1 : ℤ) ^ 1 • (H.hom 0 1 ≫ L.d 1 0) = g.f 0 - f.f 0 := by
  have he := H.comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at he
  simp only [pow_one, neg_smul, one_smul]
  rw [he]
  abel

/-- 概要：正次数の辺の評価の符号は全テンソルの水平・垂直微分に一致。
方針：ホモトピー等式を代入し、隣接する二つの符号が逆であることを使う。
規約：KST A.3・A.5、垂直微分の符号は (−1)^(p+1)。
使われ方：第一因子の正次数の鎖区間条件。 -/
lemma chainIntervalHomotopySign_succ (p : ℕ) :
    (-1 : ℤ) ^ (p + 2) • (H.hom (p + 1) (p + 2) ≫ L.d (p + 2) (p + 1)) =
      (-1 : ℤ) ^ (p + 1) • (K.d (p + 1) p ≫ H.hom p (p + 1)) +
        (-1 : ℤ) ^ (p + 1) • (g.f (p + 1) - f.f (p + 1)) := by
  have he := H.comm (p + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at he
  rw [he]
  rw [show p + 2 = (p + 1) + 1 from rfl, pow_succ, mul_neg_one, neg_smul]
  simp only [smul_sub, smul_add]
  abel

end SerrePositivity.KST.ProExcision
