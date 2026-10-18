module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCochainComponent

/-!
# 負の次数における shuffle 成分の値

概要：Berger–Fresse §1.1.3 の整数次数の shuffle 成分を自然数の鎖次数の公式で評価する。
方針：非正整数を自然数の負号として指定し、次数の標準同型を通じて成分を簡約する。
規約：入力次数は −p,−q、出力次数は −(p+q) とする。
使われ方：整数コチェイン成分の微分の両立性を正規化鎖の Leibniz 則に帰着する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：負の次数の shuffle 双線形写像は正規化鎖の shuffle の移送である（Berger–Fresse §1.1.3）。
方針：非正性による分岐と自然数への変換を簡約して標準同型を同定する。
規約：次数 −p の元を p 次の正規化鎖へ移す。
使われ方：整数コチェイン成分の値を鎖次数の公式で計算する。 -/
lemma cochainShuffleBilinear_neg (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (complex A (m + 1)).X (-(p : ℤ))) (y : (complex A n).X (-(q : ℤ))) :
    cochainShuffleBilinear A m n i (-(p : ℤ)) (-(q : ℤ)) (-((p + q : ℕ) : ℤ)) (by omega)
        x y =
      (complexXIso A (m + n) (p + q)).inv
        (shuffleBilinear A m n i p q ((complexXIso A (m + 1) p).hom x)
          ((complexXIso A n q).hom y)) := by
  rw [cochainShuffleBilinear_of_nonpos A m n i _ _ _ _ (by omega) (by omega)]
  cases p <;> cases q <;> rfl

/-- 概要：負の次数の純粋テンソル上の成分は鎖次数の shuffle で評価される（Berger–Fresse §1.1.3）。
方針：純粋テンソルの評価と双線形写像の負の次数の公式を組み合わせる。
規約：テンソルの因子の順は shuffle の入力の順と一致する。
使われ方：テンソルからの射の微分の両立性を純粋テンソル上で検証する。 -/
lemma cochainShuffleComponent_neg_tmul (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (complex A (m + 1)).X (-(p : ℤ))) (y : (complex A n).X (-(q : ℤ))) :
    cochainShuffleComponent A m n i (-(p : ℤ)) (-(q : ℤ)) (-((p + q : ℕ) : ℤ)) (by omega)
        (x ⊗ₜ[A] y) =
      (complexXIso A (m + n) (p + q)).inv
        (shuffleBilinear A m n i p q ((complexXIso A (m + 1) p).hom x)
          ((complexXIso A n q).hom y)) := by
  rw [cochainShuffleComponent_tmul, cochainShuffleBilinear_neg]

end SerrePositivity.EInfinity.BarrattEccles
