module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCochainLeibniz
public import SerrePositivity.DifferentialGraded.Complexes.Composition

/-!
# Barratt–Eccles の shuffle 部分合成の chain map

概要：Berger–Fresse §1.1.3 の shuffle 部分合成を整数コチェイン複体の射として構成する。
方針：全整数次数の Leibniz 則を成分の微分条件へ直し、既存の全テンソルの普遍性を適用する。
規約：非有界コチェイン複体の既存の Koszul テンソルを使う。
使われ方：Barratt–Eccles オペラッドの部分合成の射を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：shuffle のテンソル成分はコチェイン微分と両立する（Berger–Fresse §1.1.3）。
方針：加群テンソルの純粋テンソルで外延性を使い、全整数次数の双線形 Leibniz 則へ帰着する。
規約：右の微分項の Koszul 符号は第一の入力の整数次数で決まる。
使われ方：全テンソルからの射の普遍性に渡す微分条件である。 -/
lemma cochainShuffleComponent_d (m n : ℕ) (i : Fin (m + 1)) (r s : ℤ) :
    cochainShuffleComponent A m n i r s (r + s) rfl ≫
        (complex A (m + n)).d (r + s) (r + s + 1) =
      ((complex A (m + 1)).d r (r + 1) ▷ (complex A n).X s) ≫
        cochainShuffleComponent A m n i (r + 1) s (r + s + 1) (by omega) +
      r.negOnePow • (((complex A (m + 1)).X r ◁ (complex A n).d s (s + 1)) ≫
        cochainShuffleComponent A m n i r (s + 1) (r + s + 1) (by omega)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (complex A (m + n)).d (r + s) (r + s + 1)
      (cochainShuffleBilinear A m n i r s (r + s) rfl x y) =
    cochainShuffleBilinear A m n i (r + 1) s (r + s + 1) (by omega)
      ((complex A (m + 1)).d r (r + 1) x) y +
    r.negOnePow • cochainShuffleBilinear A m n i r (s + 1) (r + s + 1) (by omega) x
      ((complex A n).d s (s + 1) y)
  exact cochainShuffleBilinear_d A m n i r s x y

/-- 概要：Barratt–Eccles の shuffle 部分合成の複体の射（Berger–Fresse §1.1.3）。
方針：整数次数の成分と証明済みの微分の両立性に全テンソルの普遍性を適用する。
規約：外側の arity は m+1、内側は n、出力は m+n である。
使われ方：Barratt–Eccles オペラッドの comp のデータを与える。 -/
def partialComposition (m n : ℕ) (i : Fin (m + 1)) :
    complex A (m + 1) ⊗ complex A n ⟶ complex A (m + n) :=
  tensorLift (cochainShuffleComponent A m n i) (cochainShuffleComponent_d A m n i)

/-- 概要：部分合成の斉次成分は指定した shuffle 成分に一致する（Berger–Fresse §1.1.3）。
方針：全テンソルからの射の構成における直和の普遍性を使う。
規約：r+s=t の任意の次数の等式について述べる。
使われ方：部分合成の等変性と結合則を成分で検証する。 -/
@[reassoc (attr := simp)]
lemma ι_partialComposition (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t) :
    ιTensorObj (complex A (m + 1)) (complex A n) r s t h ≫
        (partialComposition A m n i).f t = cochainShuffleComponent A m n i r s t h :=
  ι_tensorLift _ _ r s t h

/-- 概要：負の次数の純粋テンソル上の部分合成の値（Berger–Fresse §1.1.3）。
方針：斉次成分の公式と正規化鎖の shuffle への評価公式を使う。
規約：入力次数 −p,−q の出力次数は −(p+q) である。
使われ方：部分合成の法則を正規化生成元上の計算へ帰着する。 -/
lemma partialComposition_neg_tmul (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (complex A (m + 1)).X (-(p : ℤ))) (y : (complex A n).X (-(q : ℤ))) :
    (partialComposition A m n i).f (-((p + q : ℕ) : ℤ))
        (ιTensorObj (complex A (m + 1)) (complex A n) (-(p : ℤ)) (-(q : ℤ))
          (-((p + q : ℕ) : ℤ)) (by omega) (x ⊗ₜ[A] y)) =
      (complexXIso A (m + n) (p + q)).inv
        (shuffleBilinear A m n i p q ((complexXIso A (m + 1) p).hom x)
          ((complexXIso A n q).hom y)) := by
  have h := congrArg (fun f => f (x ⊗ₜ[A] y))
    (ι_partialComposition A m n i (-(p : ℤ)) (-(q : ℤ)) (-((p + q : ℕ) : ℤ)) (by omega))
  exact h.trans (cochainShuffleComponent_neg_tmul A m n i p q x y)

end SerrePositivity.EInfinity.BarrattEccles
