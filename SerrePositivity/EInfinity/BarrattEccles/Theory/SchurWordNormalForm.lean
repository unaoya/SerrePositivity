module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurBasisImages

/-!
# Schur の語の基底の非正次数での表示

## 概要
Berger–Fresse §1.1 の非正次数の係数と入力の語で、全ての基底添字を表す。

## 方針
正次数の係数の空添字を除き、係数の次数を負の自然数として書く。

## 規約
元の基底添字と入力の重みを保持する。

## 使われ方
全てのセルの基底語について微分の重みを評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles

/-- Every word index has a normalized nonpositive coefficient degree and the specified inputs. -/
lemma schurWordIndex_exists_nonpositive {I : ℤ → Type u} (i : ℤ) (x : SchurWordIndex I i) :
    ∃ (n q : ℕ) (a : ULift.{u} (BasedNondegenerate n q))
      (v : powerGradedIndex I n (i + q)),
        schurNonpositiveWordIndex i n q (a, v) = x := by
  classical
  obtain ⟨n, ⟨⟨p, r⟩, h⟩, x⟩ := x
  by_cases hp : p ≤ 0
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, p = -(q : ℤ) := ⟨(-p).toNat, by omega⟩
    subst p
    have hr : r = i + q := by omega
    subst r
    let y : ULift.{u} (BasedNondegenerate n q) × powerGradedIndex I n (i + q) := by
      simpa only [schurWordPieceIndex, ite_eq_left (show -(q : ℤ) ≤ 0 by omega),
        neg_neg, Int.toNat_natCast] using x
    refine ⟨n, q, y.1, y.2, ?_⟩
    cases q <;> simp [schurNonpositiveWordIndex, y]
  · have y : PEmpty := by
      simpa only [schurWordPieceIndex, ite_eq_right hp] using x
    exact y.elim

end SerrePositivity.EInfinity.BarrattEccles
