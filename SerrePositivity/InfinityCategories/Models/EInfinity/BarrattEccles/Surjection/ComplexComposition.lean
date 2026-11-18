module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CochainLeibniz
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
模型。文献の定義との比較は後で
# 全射語の整数複体の部分合成射

概要：Berger–Fresse §1.2.4–5 の χ の部分合成を整数複体のテンソルからの射へまとめる。
方針：双線形合成の全整数 Leibniz 則を加群テンソルの微分条件へ移し、tensorLift を使う。
規約：非有界整数コチェインと既存の Koszul テンソルを使う。
使われ方：χ の Operad の comp と TR オペラッド射の合成保存。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：χ の整数合成のテンソル成分は微分と両立（BF §1.2.3–5）。
方針：純粋テンソルで全整数双線形 Leibniz 則へ帰着する。
規約：右微分項の符号は第一の整数次数で決まる。
使われ方：tensorLift の微分条件。 -/
lemma cochainCompositionComponent_d (m n : ℕ) (i : Fin (m + 1)) (r s : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionComponent A m n i r s (r + s) rfl ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + n)).d (r + s) (r + s + 1) =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)).d r (r + 1) ▷ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X s) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionComponent A m n i (r + 1) s (r + s + 1) (by omega) +
      r.negOnePow • (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)).X r ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).d s (s + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionComponent A m n i r (s + 1) (r + s + 1) (by omega)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionBilinear_d A m n i r s x y

/-- 概要：χ の部分合成の整数コチェイン複体の射（BF §1.2.4–5）。
方針：全次数のテンソル成分と微分条件を tensorLift へ渡す。
規約：外側 arity は m+1、内側 n、出力 m+n。
使われ方：χ オペラッドの comp 成分。 -/
def complexPartialComposition (m n : ℕ) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + n) :=
  tensorLift (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionComponent A m n i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionComponent_d A m n i)

/-- 概要：部分合成射の斉次成分は指定した全射語合成成分（BF §1.2.4–5）。
方針：全テンソルの直和の普遍性を評価する。
規約：全整数入力次数と和の任意の等式。
使われ方：複体射の法則と TR の合成保存を成分で調べる。 -/
@[reassoc (attr := simp)] lemma ι_complexPartialComposition (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t) :
    ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) r s t h ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m n i).f t = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionComponent A m n i r s t h :=
  ι_tensorLift _ _ r s t h

/-- 概要：負の純粋テンソル上の複体射の合成は全射語の部分合成（BF §1.2.4–5）。
方針：斉次成分の式と整数双線形合成の負次数の公式を評価する。
規約：入力の順は外側・内側。
使われ方：χ の複体射の結合則を成分法則から確認する。 -/
lemma complexPartialComposition_neg_tmul (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)).X (-(p : ℤ))) (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X (-(q : ℤ))) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m n i).f (-((p + q : ℕ) : ℤ))
        (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (-(p : ℤ)) (-(q : ℤ))
          (-((p + q : ℕ) : ℤ)) (by omega) (x ⊗ₜ[A] y)) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (m + n) (p + q)).inv
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n p q i ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (m + 1) p).hom x)
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n q).hom y)) := by
  have h := congrArg (fun f => f (x ⊗ₜ[A] y))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ι_complexPartialComposition A m n i (-(p : ℤ)) (-(q : ℤ))
      (-((p + q : ℕ) : ℤ)) (by omega))
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.cochainCompositionBilinear_neg A m n i p q x y)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
