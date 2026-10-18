module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCochainDegrees
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLeibnizChains

/-!
# 整数コチェイン次数の shuffle 成分

概要：Berger–Fresse §1.1.3 の正規化鎖上の shuffle を整数次数の双線形成分へ移す。
方針：両次数が非正なら標準同型で鎖次数へ移し、正次数の入力では零写像を使う。
規約：次数 r,s の入力を r+s 次へ送り、成分は既存の加群テンソルからの射に線形化する。
使われ方：既存のコチェインテンソル複体の普遍性へ渡す成分族となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory

variable (A : Type u) [CommRing A]

/-- 概要：非正次数の入力に対する整数次数の shuffle 双線形写像（Berger–Fresse §1.1.3）。
方針：入力を正規化鎖へ移し、shuffle の後で出力の鎖次数を移送して元の複体へ戻す。
規約：出力次数 t は r+s に等しく、両入力次数は非正である。
使われ方：全整数次数の shuffle 成分の非零の分岐を与える。 -/
def cochainShuffleBilinearNonpos (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t) (hr : r ≤ 0) (hs : s ≤ 0) :
    (complex A (m + 1)).X r →ₗ[A] (complex A n).X s →ₗ[A] (complex A (m + n)).X t :=
  ((((shuffleBilinear A m n i (-r).toNat (-s).toNat).comp
    (complexXIsoNonpos A (m + 1) r hr).hom.hom).compl₂
      (complexXIsoNonpos A n s hs).hom.hom).compr₂
        (((complexXIsoNonpos A (m + n) t (by omega)).inv.hom).comp
          (degreeTransport A (m + n) (by omega : (-r).toNat + (-s).toNat = (-t).toNat))))

/-- 概要：全整数次数で定義した shuffle 双線形写像（Berger–Fresse §1.1.3）。
方針：非正次数の分岐では鎖次数の shuffle を使い、それ以外は零とする。
規約：正次数の成分は零対象なので零写像が唯一の可能性である。
使われ方：加群テンソルからの shuffle の成分を作る。 -/
def cochainShuffleBilinear (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t) :
    (complex A (m + 1)).X r →ₗ[A] (complex A n).X s →ₗ[A] (complex A (m + n)).X t :=
  if hr : r ≤ 0 then
    if hs : s ≤ 0 then cochainShuffleBilinearNonpos A m n i r s t h hr hs else 0
  else 0

/-- 概要：非正次数では全次数の shuffle は非正次数の公式に一致する（Berger–Fresse §1.1.3）。
方針：二つの次数の条件によって分岐を簡約する。
規約：非正性の証明の選択に依存しない。
使われ方：微分の両立性を鎖次数の計算へ帰着する。 -/
lemma cochainShuffleBilinear_of_nonpos (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t) (hr : r ≤ 0) (hs : s ≤ 0) :
    cochainShuffleBilinear A m n i r s t h =
      cochainShuffleBilinearNonpos A m n i r s t h hr hs := by
  simp only [cochainShuffleBilinear, dite_eq_left hr, dite_eq_left hs]

/-- 概要：正次数の第一の入力に対する shuffle 成分は零である（Berger–Fresse §1.1.3）。
方針：第一の次数の非正性の分岐を除く。
規約：第二の次数には制限を置かない。
使われ方：入力の正次数成分が零である場合の微分の等式を処理する。 -/
lemma cochainShuffleBilinear_eq_zero_of_left_pos (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t) (hr : 0 < r) :
    cochainShuffleBilinear A m n i r s t h = 0 := by
  simp only [cochainShuffleBilinear, dite_eq_right (not_le_of_gt hr)]

/-- 概要：正次数の第二の入力に対する shuffle 成分は零である（Berger–Fresse §1.1.3）。
方針：第一の次数で場合分けし、第二の次数の非正性の分岐を除く。
規約：第一の次数には制限を置かない。
使われ方：入力の正次数成分が零である場合の微分の等式を処理する。 -/
lemma cochainShuffleBilinear_eq_zero_of_right_pos (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t) (hs : 0 < s) :
    cochainShuffleBilinear A m n i r s t h = 0 := by
  unfold cochainShuffleBilinear
  by_cases hr : r ≤ 0
  · rw [dite_eq_left hr, dite_eq_right (not_le_of_gt hs)]
  · rw [dite_eq_right hr]

/-- 概要：加群テンソル上の shuffle の斉次成分（Berger–Fresse §1.1.3）。
方針：整数次数の shuffle 双線形写像をテンソル積の普遍性で線形化する。
規約：出力次数は明示された和の等式で指定する。
使われ方：コチェイン複体のテンソルからの chain map を構成する入力となる。 -/
def cochainShuffleComponent (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t) :
    (complex A (m + 1)).X r ⊗ (complex A n).X s ⟶ (complex A (m + n)).X t :=
  ModuleCat.ofHom (TensorProduct.lift (cochainShuffleBilinear A m n i r s t h))

/-- 概要：純粋テンソル上の shuffle 成分の値（Berger–Fresse §1.1.3）。
方針：テンソル積の普遍性による線形化を評価する。
規約：テンソル積の因子の順は外側の演算、内側の演算である。
使われ方：成分の微分の両立性を双線形写像の等式へ帰着する。 -/
@[simp] lemma cochainShuffleComponent_tmul (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t)
    (x : (complex A (m + 1)).X r) (y : (complex A n).X s) :
    cochainShuffleComponent A m n i r s t h (x ⊗ₜ[A] y) =
      cochainShuffleBilinear A m n i r s t h x y := rfl

end SerrePositivity.EInfinity.BarrattEccles
