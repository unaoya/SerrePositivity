module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComplexDegrees
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Composition
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Transports

/-!
模型。文献の定義との比較は後で
# 整数コチェイン次数の全射語の部分合成

概要：Berger–Fresse §1.2.4–5 の部分合成を全整数次数の双線形成分へ移す。
方針：非正次数を鎖次数へ戻し、部分合成と次数移送の後に整数成分へ戻す。
規約：正次数の入力では零写像。係数環と arity に制限を課さない。
使われ方：全テンソル複体からの部分合成射を構成する成分族。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable (A : Type u) [CommRing A]

/-- 概要：非正整数次数での全射語の双線形部分合成（BF §1.2.4–5）。
方針：入力を全射語加群へ移し、既存の部分合成を等しい出力次数へ移送する。
規約：出力整数次数 t は r+s に等しい。
使われ方：全整数成分の非零の分岐。 -/
def cochainCompositionNonpos (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t) (hr : r ≤ 0) (hs : s ≤ 0) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)).X r →ₗ[A] (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X s →ₗ[A] (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + n)).X t :=
  ((((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n (-r).toNat (-s).toNat i).comp
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIsoNonpos A (m + 1) r hr).hom.hom).compl₂
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIsoNonpos A n s hs).hom.hom).compr₂
        (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIsoNonpos A (m + n) t (by omega)).inv.hom).comp
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeTransport A (m + n) (by omega : (-r).toNat + (-s).toNat = (-t).toNat))))

/-- 概要：全整数次数の双線形部分合成（BF §1.2.4–5）。
方針：非正入力では全射語の合成を使い、正次数では零とする。
規約：正次数成分は零対象なので、この分岐の写像は一意。
使われ方：加群テンソル上の合成成分を定義する。 -/
def cochainCompositionBilinear (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)).X r →ₗ[A] (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X s →ₗ[A] (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + n)).X t :=
  if hr : r ≤ 0 then
    if hs : s ≤ 0 then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionNonpos A m n i r s t h hr hs else 0
  else 0

/-- 概要：非正入力では全整数合成は非正次数の公式（BF §1.2.4–5）。
方針：二つの分岐を簡約する。
規約：非正性の証明には依存しない。
使われ方：TR の一般の鎖合成保存へ比較する。 -/
lemma cochainCompositionBilinear_of_nonpos (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t) (hr : r ≤ 0) (hs : s ≤ 0) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionBilinear A m n i r s t h =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionNonpos A m n i r s t h hr hs := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionBilinear, dite_eq_left hr, dite_eq_left hs]

/-- 概要：負の整数次数の合成は本来の全射語の合成（BF §1.2.4–5）。
方針：非正分岐を評価し、自然数への変換と比較同型を同定する。
規約：入力次数は −p・−q、出力は −(p+q)。
使われ方：複体射の評価を証明済みの成分の結合則へ戻す。 -/
lemma cochainCompositionBilinear_neg (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)).X (-(p : ℤ))) (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X (-(q : ℤ))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionBilinear A m n i (-(p : ℤ)) (-(q : ℤ))
        (-((p + q : ℕ) : ℤ)) (by omega) x y =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (m + n) (p + q)).inv
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n p q i ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (m + 1) p).hom x)
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n q).hom y)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionBilinear_of_nonpos A m n i _ _ _ _ (by omega) (by omega)]
  cases p <;> cases q <;> rfl

/-- 概要：全射語の整数合成をテンソル成分へ線形化する（BF §1.2.4–5）。
方針：加群テンソルの普遍性を双線形合成へ適用する。
規約：因子順は外側演算と内側演算。
使われ方：tensorLift に渡す合成成分。 -/
def cochainCompositionComponent (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)).X r ⊗ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X s ⟶ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + n)).X t :=
  ModuleCat.ofHom (TensorProduct.lift (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionBilinear A m n i r s t h))

/-- 概要：純粋テンソル上の整数合成成分は双線形合成（BF §1.2.4–5）。
方針：テンソルの普遍性による写像を評価する。
規約：出力の和の証明は任意。
使われ方：複体射の微分条件と合成保存の元での計算。 -/
@[simp] lemma cochainCompositionComponent_tmul (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t)
    (x : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)).X r) (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X s) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionComponent A m n i r s t h (x ⊗ₜ[A] y) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionBilinear A m n i r s t h x y := rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
