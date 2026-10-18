module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSwapFaces

/-!
# 正規化鎖の次数の等式による移送

概要：Berger–Fresse §1.1.3 の shuffle の微分で現れる出力次数の等式を扱う。
方針：等式から得られる複体の成分間の線形写像を使い、面を頂点ごとに比較する。
規約：次数を移しても有限頂点の自然数としての番号は変えない。
使われ方：水平・垂直方向の寄与を共通の出力次数へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：次数の等式による正規化鎖の成分間の線形写像（Berger–Fresse §1.1.3）。
方針：複体の成分へ次数の等式を適用し、得られた等式の射を取る。
規約：追加の同型や基底の選択を含まない。
使われ方：微分の出力次数の括弧の違いを移す。 -/
def degreeTransport (A : Type u) [CommRing A] (n : ℕ) {r t : ℕ} (h : r = t) :
    (normalizedChains A n).X r →ₗ[A] (normalizedChains A n).X t :=
  (eqToHom (congrArg (normalizedChains A n).X h)).hom

/-- 概要：同じ次数への移送は恒等写像である（Berger–Fresse §1.1.3）。
方針：等式の射を定義展開する。
規約：等式の証明の選び方に依存しない。
使われ方：次数移送の計算を簡約する。 -/
@[simp] lemma degreeTransport_refl (A : Type u) [CommRing A] (n r : ℕ)
    (z : (normalizedChains A n).X r) : degreeTransport A n rfl z = z := rfl

/-- 概要：頂点番号が対応する二つの面の正規化生成元は次数の移送で一致する（Berger–Fresse §1.1.3）。
方針：次数の等式を消去し、置換列の各頂点で面写像を比較する。
規約：二つの面写像の値は Fin.cast を介して一致すると仮定する。
使われ方：異なる括弧の出力次数で計算した境界項を同定する。 -/
lemma degreeTransport_generator_map (A : Type u) [CommRing A] (n N : ℕ)
    {r t : ℕ} (h : r = t) (f : ⦋r⦌ ⟶ ⦋N⦌) (g : ⦋t⦌ ⟶ ⦋N⦌)
    (hfg : ∀ k : Fin (t + 1),
      f.toOrderHom (Fin.cast (congrArg (fun d => d + 1) h.symm) k) = g.toOrderHom k)
    (x : (simplicial n) _⦋N⦌) :
    degreeTransport A n h (normalizedGenerator A n r ((simplicial n).map f.op x)) =
      normalizedGenerator A n t ((simplicial n).map g.op x) := by
  cases h
  rw [degreeTransport_refl]
  apply congrArg (normalizedGenerator A n r)
  apply (simplexEquiv n r).injective
  funext k
  simp only [simplexEquiv_map]
  exact congrArg (simplexEquiv n N x) (hfg k)

end SerrePositivity.EInfinity.BarrattEccles
