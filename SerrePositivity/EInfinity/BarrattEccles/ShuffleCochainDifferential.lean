module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleNegativeComponent

/-!
# 負の整数次数における shuffle と微分

概要：Berger–Fresse §1.1.3 の鎖次数の Leibniz 則を負のコチェイン次数へ移す。
方針：成分の評価公式と次数同型の微分との可換性を使い、Koszul 符号を整数の符号へ直す。
規約：鎖次数の和と出力次数の同定は degreeTransport で明示する。
使われ方：テンソル複体からの射の成分の微分条件を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：負の次数の shuffle の出力を任意の等しい鎖次数で指定する（Berger–Fresse §1.1.3）。
方針：次数の等式を消去して標準の負次数の評価公式を適用する。
規約：p+q=k の移送は正規化鎖の出力に作用する。
使われ方：Leibniz 則の二つの微分項の出力次数を揃える。 -/
lemma cochainShuffleBilinear_neg_output (m n : ℕ) (i : Fin (m + 1)) (p q k : ℕ)
    (h : p + q = k) (x : (complex A (m + 1)).X (-(p : ℤ)))
    (y : (complex A n).X (-(q : ℤ))) :
    cochainShuffleBilinear A m n i (-(p : ℤ)) (-(q : ℤ)) (-(k : ℤ)) (by omega) x y =
      (complexXIso A (m + n) k).inv (degreeTransport A (m + n) h
        (shuffleBilinear A m n i p q ((complexXIso A (m + 1) p).hom x)
          ((complexXIso A n q).hom y))) := by
  subst k
  rw [degreeTransport_refl]
  exact cochainShuffleBilinear_neg A m n i p q x y

/-- 概要：次数同型の逆写像を通した微分の元での公式（Berger–Fresse §1.1.2）。
方針：逆同型と微分の可換性を元に評価する。
規約：鎖次数 p から q の任意の微分を扱う。
使われ方：shuffle の出力の微分を正規化鎖で計算する。 -/
lemma complexXIso_inv_d_apply (n p q : ℕ) (z : (normalizedChains A n).X p) :
    (complex A n).d (-(p : ℤ)) (-(q : ℤ)) ((complexXIso A n p).inv z) =
      (complexXIso A n q).inv ((normalizedChains A n).d p q z) :=
  congrArg (fun f => f z) (complexXIso_inv_d A n p q)

/-- 概要：次数同型の順写像を通した微分の元での公式（Berger–Fresse §1.1.2）。
方針：順同型と微分の可換性を元に評価する。
規約：鎖次数 p から q の任意の微分を扱う。
使われ方：shuffle の入力の微分を正規化鎖で計算する。 -/
lemma complexXIso_hom_d_apply (n p q : ℕ) (z : (complex A n).X (-(p : ℤ))) :
    (complexXIso A n q).hom ((complex A n).d (-(p : ℤ)) (-(q : ℤ)) z) =
      (normalizedChains A n).d p q ((complexXIso A n p).hom z) :=
  congrArg (fun f => f z) (complexXIso_hom_d A n p q)

/-- 概要：両入力が負の整数次数の shuffle はコチェインの Leibniz 則を満たす（Berger–Fresse §1.1.3）。
方針：全成分を正規化鎖へ移し、鎖次数の Leibniz 則を適用して整数の符号を同定する。
規約：入力次数は −(p+1),−(q+1) である。
使われ方：負の入力次数の場合のテンソル成分の微分条件となる。 -/
lemma cochainShuffleBilinear_d_negative (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (complex A (m + 1)).X (-((p + 1 : ℕ) : ℤ)))
    (y : (complex A n).X (-((q + 1 : ℕ) : ℤ))) :
    (complex A (m + n)).d (-((p + 1 + (q + 1) : ℕ) : ℤ)) (-((p + 1 + q : ℕ) : ℤ))
        (cochainShuffleBilinear A m n i (-((p + 1 : ℕ) : ℤ)) (-((q + 1 : ℕ) : ℤ))
          (-((p + 1 + (q + 1) : ℕ) : ℤ)) (by omega) x y) =
      cochainShuffleBilinear A m n i (-(p : ℤ)) (-((q + 1 : ℕ) : ℤ))
        (-((p + 1 + q : ℕ) : ℤ)) (by omega)
        ((complex A (m + 1)).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) x) y +
      (-((p + 1 : ℕ) : ℤ)).negOnePow •
        cochainShuffleBilinear A m n i (-((p + 1 : ℕ) : ℤ)) (-(q : ℤ))
          (-((p + 1 + q : ℕ) : ℤ)) (by omega) x
          ((complex A n).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) y) := by
  rw [cochainShuffleBilinear_neg_output A m n i (p + 1) (q + 1) _ rfl,
    cochainShuffleBilinear_neg_output A m n i p (q + 1) _ (by omega),
    cochainShuffleBilinear_neg_output A m n i (p + 1) q _ rfl]
  simp only [degreeTransport_refl]
  rw [complexXIso_inv_d_apply A (m + n), complexXIso_hom_d_apply A (m + 1),
    complexXIso_hom_d_apply A n, shuffleBilinear_d_positive A m n i p q]
  simp only [map_add, map_zsmul, Units.smul_def, Int.negOnePow_neg, Int.coe_negOnePow_natCast]

/-- 概要：第一の入力が次数0の場合のコチェイン微分の公式（Berger–Fresse §1.1.3）。
方針：成分を正規化鎖へ移し、次数0の第一の入力の微分の公式を使う。
規約：第二の入力次数は −(q+1) である。
使われ方：全整数次数の成分の微分条件の次数0の分岐となる。 -/
lemma cochainShuffleBilinear_d_leftZero (m n : ℕ) (i : Fin (m + 1)) (q : ℕ)
    (x : (complex A (m + 1)).X 0) (y : (complex A n).X (-((q + 1 : ℕ) : ℤ))) :
    (complex A (m + n)).d (-((0 + (q + 1) : ℕ) : ℤ)) (-((0 + q : ℕ) : ℤ))
        (cochainShuffleBilinear A m n i 0 (-((q + 1 : ℕ) : ℤ))
          (-((0 + (q + 1) : ℕ) : ℤ)) (by omega) x y) =
      cochainShuffleBilinear A m n i 0 (-(q : ℤ)) (-((0 + q : ℕ) : ℤ)) (by omega) x
        ((complex A n).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) y) := by
  erw [cochainShuffleBilinear_neg_output A m n i 0 (q + 1) _ rfl,
    cochainShuffleBilinear_neg_output A m n i 0 q _ rfl]
  simp only [degreeTransport_refl]
  rw [complexXIso_inv_d_apply A (m + n), complexXIso_hom_d_apply A n,
    shuffleBilinear_d_leftZero A m n i q]

/-- 概要：第二の入力が次数0の場合のコチェイン微分の公式（Berger–Fresse §1.1.3）。
方針：成分を正規化鎖へ移し、次数0の第二の入力の微分の公式を使う。
規約：第一の入力次数は −(p+1) である。
使われ方：全整数次数の成分の微分条件の次数0の分岐となる。 -/
lemma cochainShuffleBilinear_d_rightZero (m n : ℕ) (i : Fin (m + 1)) (p : ℕ)
    (x : (complex A (m + 1)).X (-((p + 1 : ℕ) : ℤ))) (y : (complex A n).X 0) :
    (complex A (m + n)).d (-((p + 1 + 0 : ℕ) : ℤ)) (-((p + 0 : ℕ) : ℤ))
        (cochainShuffleBilinear A m n i (-((p + 1 : ℕ) : ℤ)) 0
          (-((p + 1 + 0 : ℕ) : ℤ)) (by omega) x y) =
      cochainShuffleBilinear A m n i (-(p : ℤ)) 0 (-((p + 0 : ℕ) : ℤ)) (by omega)
        ((complex A (m + 1)).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) x) y := by
  erw [cochainShuffleBilinear_neg_output A m n i (p + 1) 0 _ rfl,
    cochainShuffleBilinear_neg_output A m n i p 0 _ rfl]
  simp only [degreeTransport_refl]
  rw [complexXIso_inv_d_apply A (m + n), complexXIso_hom_d_apply A (m + 1),
    shuffleBilinear_d_rightZero A m n i p]

/-- 概要：正整数次数の成分の全ての元は零である（Berger–Fresse §1.1.2）。
方針：正次数の零対象性を加群の元の一意性へ直す。
規約：コチェイン次数が正である場合に限る。
使われ方：正次数を含むテンソル成分の微分条件を処理する。 -/
lemma complex_eq_zero_of_positive (n : ℕ) (r : ℤ) (hr : 0 < r) (x : (complex A n).X r) :
    x = 0 := by
  let _ := ModuleCat.isZero_iff_subsingleton.mp (complex_isZero_positive A n r hr)
  exact Subsingleton.elim _ _

end SerrePositivity.EInfinity.BarrattEccles
