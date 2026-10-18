module

public import SerrePositivity.EInfinity.Operad.OneSlotSubstitutionTransport
public import SerrePositivity.EInfinity.Operad.TensorSubstitutionMiddle

/-!
# 末尾を固定する交換後の反復合成の因子分解

概要：Berger–Moerdijk §1 の末尾以外の隣接交換の後の反復合成の再帰を正規化する。
方針：最後の入力の分離と一回の代入を明示し、入力データの移送を適用する。
規約：最後の指定入力と元の未代入入力は保つ。
使われ方：反復合成の隣接交換の外側等変性の帰納段階へ適用する。
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
  tensorSubstitutionStep composeFirstInputs

/-- 概要：反復合成の一段を最後の分離と一回の代入、残りの反復合成に分ける（Berger–Moerdijk §1）。
方針：既存の再帰の因子分解で終域の移送を代入射全体の後へ出す。
規約：最初の代入射に始域と中間の arity の移送を含める。
使われ方：交換前後の反復合成を同じ再帰の形で比較する。 -/
lemma composeFirstInputs_oneSlot_after_factor (P : Operad A) (n k : ℕ)
    (s : Fin (n + 1) → ℕ) :
    P.composeFirstInputs (n + 1) k s =
      (P.arity (n + 1 + k) ◁ (tensorFamilySplitLast n (fun j => P.arity (s j))).hom) ≫
        tensorSubstitutionStep (P.composeFirstInputInsertion n k (s (Fin.last n)))
          (P.composeFirstInputs n (k + s (Fin.last n)) (fun j => s j.castSucc)) ≫
        eqToHom (congrArg P.arity (oneSlotComposeOutput_eq n k s)) := by
  rw [P.composeFirstInputs_succ_factor]
  simp only [tensorFamilySubstitutionStep, tensorSubstitutionStep_post, composeFirstInputInsertion]

/-- 概要：末尾以外の隣接交換後の反復合成は元の最後の arity と交換した前半で因子分解できる（Berger–Moerdijk §1）。
方針：交換後の再帰の因子分解へ入力データの移送の等式を適用する。
規約：交換後の分離の終域を移す等式の射を明示する。
使われ方：分離同型の可換性と帰納仮定を元の反復合成へ接続する。 -/
lemma composeFirstInputs_adjacent_cast_factor (P : Operad A) (n k : ℕ)
    (s : Fin (n + 2) → ℕ) (i : Fin n) :
    let w := fun j => s (adjacentTransposition i.castSucc j)
    let l := s (Fin.last (n + 1))
    let R := P.arity (n + 2 + k)
    P.composeFirstInputs (n + 2) k w =
      (R ◁ (tensorFamilySplitLast (n + 1) (fun j => P.arity (w j))).hom) ≫
        (R ◁ eqToHom (tensorFamily_adjacentCastSucc_output_obj n (fun j => P.arity (s j)) i)) ≫
        tensorSubstitutionStep (P.composeFirstInputInsertion (n + 1) k l)
          (P.composeFirstInputs (n + 1) (k + l) (fun j => s (adjacentTransposition i j).castSucc)) ≫
        eqToHom (congrArg P.arity (oneSlotSwapOutput_eq n k s i)) := by
  dsimp only
  have h := P.composeFirstInputs_oneSlot_after_factor (n + 1) k
    (fun j => s (adjacentTransposition i.castSucc j))
  conv_rhs at h =>
    arg 2
    rw [P.oneSlotSubstitution_adjacent_transport n k s i]
  exact h

end SerrePositivity.EInfinity.Operad
