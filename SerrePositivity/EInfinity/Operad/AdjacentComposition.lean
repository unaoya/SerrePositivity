module

public import SerrePositivity.EInfinity.Operad.AdjacentSlotBlockSwap
public import SerrePositivity.EInfinity.Operad.TwoSlotComposition

/-!
# 隣接二入力への合成のブロック交換による等変性

概要：Berger–Moerdijk §1 の隣接二入力への合成の外側等変性を、標準のブロック交換で記述する。
方針：二位置への一般の合成の等変性に、出力の全単射の四区間による同定を適用する。
規約：前方 p 個と後方 q 個の入力を保持する。
使われ方：全入力への反復合成の外側等変性の末尾二入力の交換へ適用する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：隣接二入力への合成の外側交換は出力の二ブロックの交換を誘導する（Berger–Moerdijk §1）。
方針：二位置への合成の外側等変性と、その出力の標準ブロック交換との同定を使う。
規約：内側二因子は Koszul 対称性で交換し、前後の入力を固定する。
使われ方：反復合成の二段の交換を、内側ブロックと未代入入力の置換として扱う。 -/
lemma twoSlotComposition_adjacent_equivariance (P : Operad A) (p q a b : ℕ) :
    (P.sequence.map (FiniteBijection.permutation ((p + q) + 2)
        (Equiv.swap (⟨p, by omega⟩ : Fin ((p + q) + 2)) ⟨p + 1, by omega⟩)) ⊗ₘ
      (β_ (P.arity a) (P.arity b)).hom) ≫
        P.twoSlotComposition (p + q) b a ⟨p, by omega⟩ ⟨p + 1, by omega⟩
          (by change p < p + 1; omega) =
      P.twoSlotComposition (p + q) a b ⟨p, by omega⟩ ⟨p + 1, by omega⟩
          (by change p < p + 1; omega) ≫
        P.sequence.map (FiniteBijection.homOfEquiv
          (X := FiniteBijection.of (((p + q) + a) + b))
          (Y := FiniteBijection.of (((p + q) + b) + a)) (operadContextBlockSwap p q a b)) := by
  have h := P.twoSlotComposition_outer_equivariance (p + q) a b
    (⟨p, by omega⟩ : Fin ((p + q) + 2)) ⟨p + 1, by omega⟩
    (by change p < p + 1; omega)
  rw [← operadAdjacentSlotOutput_eq_twoSlot p q a b,
    operadAdjacentSlotOutput_eq_blockSwap] at h
  exact h

end SerrePositivity.EInfinity.Operad
