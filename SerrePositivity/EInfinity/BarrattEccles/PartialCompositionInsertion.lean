module

public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionLeftUnit

/-!
# 次の代入に合わせた部分合成の出力 arity

概要：Berger–Fresse §1.1.3 の並列代入の一回目の出力を次の外側 arity へ移す。
方針：部分合成に arity の等式の射を合成する。
規約：m+1+n を m+n+1 として扱う。
使われ方：二回の並列代入の複体の射と純粋テンソルの公式を記述する。
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

/-- 概要：並列代入の一回目の出力を次の外側 arity にする（Berger–Fresse §1.1.3）。
方針：部分合成の後に arity の等式の射を合成する。
規約：二回目の外側の arity は m+n+1 である。
使われ方：並列の部分合成の結合則の両辺を型付けする。 -/
def partialCompositionAfterInsertion (m n : ℕ) (i : Fin (m + 2)) :
    complex A (m + 2) ⊗ complex A n ⟶ complex A (m + n + 1) :=
  partialComposition A (m + 1) n i ≫
    eqToHom (congrArg (complex A) (by omega : m + 1 + n = m + n + 1))

/-- 概要：出力 arity を移した部分合成を負の斉次テンソルで計算する（Berger–Fresse §1.1.3）。
方針：部分合成の評価公式と arity の移送の自然性を使う。
規約：出力鎖次数は p+q である。
使われ方：複体の射の並列結合則を正規化鎖へ帰着する。 -/
lemma partialCompositionAfterInsertion_neg_tmul (m n : ℕ) (i : Fin (m + 2))
    (p q : ℕ) (x : (complex A (m + 2)).X (-(p : ℤ)))
    (y : (complex A n).X (-(q : ℤ))) :
    (partialCompositionAfterInsertion A m n i).f (-((p + q : ℕ) : ℤ))
        (ιTensorObj (complex A (m + 2)) (complex A n) (-(p : ℤ)) (-(q : ℤ))
          (-((p + q : ℕ) : ℤ)) (by omega) (x ⊗ₜ[A] y)) =
      (complexXIso A (m + n + 1) (p + q)).inv
        ((normalizedChainMap A (simplicialArityMap
          (by omega : m + 1 + n = m + n + 1))).f (p + q)
          (shuffleBilinear A (m + 1) n i p q ((complexXIso A (m + 2) p).hom x)
            ((complexXIso A n q).hom y))) := by
  simp only [partialCompositionAfterInsertion, HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [← normalizedFunctor_arityMap A (by omega : m + 1 + n = m + n + 1)]
  erw [partialComposition_neg_tmul A (m + 1) n i p q]
  exact complexXIso_inv_naturality_apply A
    (simplicialArityMap (by omega : m + 1 + n = m + n + 1)) (p + q) _

end SerrePositivity.EInfinity.BarrattEccles
