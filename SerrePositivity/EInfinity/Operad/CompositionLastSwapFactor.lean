module

public import SerrePositivity.EInfinity.Operad.TwoSlotSubstitutionTransport

/-!
# 交換後の反復合成の因子分解

概要：Berger–Moerdijk §1 の末尾二入力を交換した反復合成の因子分解を正規化する。
方針：実際の交換後の入力族の因子分解に、二位置への代入射の入力データの移送を適用する。
規約：前半は元の入力族の順序を保ち、二入力の arity のみ逆順にする。
使われ方：分離後の末尾交換の可換性を元の反復合成へ適用する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.Coxeter
open scoped BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  tensorSubstitutionStep composeFirstInputsAfterTwo twoSlotComposition composeFirstInputs

/-- 概要：末尾二入力を交換した反復合成を元の前半と逆順の二位置への合成に分解する（Berger–Moerdijk §1）。
方針：既存の因子分解の代入射へ入力データの移送の等式を適用する。
規約：交換後の分離の終域を正規化する等式の射を明示する。
使われ方：元の反復合成の外側等変性で分離後の可換性を用いる。 -/
lemma composeFirstInputs_lastSwap_factor (P : Operad A) (n k : ℕ)
    (s : Fin (n + 2) → ℕ) :
    let w := fun i => s (adjacentTransposition (Fin.last n) i)
    let a := s (Fin.last n).castSucc
    let b := s (Fin.last (n + 1))
    let R := P.arity ((n + k) + 2)
    P.composeFirstInputs (n + 2) k w =
      (eqToHom (congrArg P.arity (by omega : n + 2 + k = (n + k) + 2)) ▷
        tensorFamily (n + 2) (fun i => P.arity (w i))) ≫
        (R ◁ (tensorFamilySplitLastTwo n (fun i => P.arity (w i))).hom) ≫
        (R ◁ eqToHom (tensorFamily_lastSwap_output_obj n (fun i => P.arity (s i)))) ≫
        tensorSubstitutionStep
          (P.twoSlotComposition (n + k) b a ⟨n, by omega⟩ ⟨n + 1, by omega⟩
            (by change n < n + 1; omega))
          (P.composeFirstInputsAfterTwo n k b a (fun i => s i.castSucc.castSucc)) ≫
        eqToHom (congrArg P.arity (lastTwoSwapOutput_eq n k s)) := by
  dsimp only
  have h := P.composeFirstInputs_twoSlot_after_factor n k
    (fun i => s (adjacentTransposition (Fin.last n) i))
  dsimp only at h
  conv_rhs at h =>
    arg 2
    arg 2
    rw [P.twoSlotSubstitution_lastSwap_transport n k s]
  exact h

end SerrePositivity.EInfinity.Operad
