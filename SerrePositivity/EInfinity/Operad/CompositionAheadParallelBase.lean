module

public import SerrePositivity.EInfinity.Operad.CompositionAfterFlat
public import SerrePositivity.EInfinity.Operad.FirstParallelInsertion

/-!
# 先頭合成と空の後半の反復代入の交換

概要：Berger–Moerdijk §1 の先頭合成と後半の反復代入の交換則の基底を証明する。
方針：空の反復代入を単位子へ簡約し、先頭合成の arity の移送を用いる。
規約：出力の arity は p+(∑ s)+k とする。
使われ方：後半の入力数に関する帰納法を開始する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open scoped BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：先頭への部分合成は空の後半への反復代入と交換できる（Berger–Moerdijk §1）。
方針：空の族の代入と右単位子の自然性を使い、残す入力数の移送を相殺する。
規約：先頭に代入する演算の arity p は零でもよい。
使われ方：後半の有限族全体との交換則の帰納法の基底となる。 -/
lemma composeAheadOfInputs_after_zero (P : Operad A) (k p : ℕ) (s : Fin 0 → ℕ) :
    (P.composeAheadOfInputs 0 k p ▷ tensorFamily 0 (fun j => P.arity (s j))) ≫
      P.composeAfterInputsFlat p 0 k s =
    (α_ (P.arity (1 + 0 + k)) (P.arity p) (tensorFamily 0 (fun j => P.arity (s j)))).hom ≫
      tensorSubstitutionStep (P.composeAfterInputsFlat 1 0 k s)
        (P.composeAheadOfInputs (∑ j, s j) k p) := by
  rw [P.composeAfterInputsFlat_zero p k s, P.composeAfterInputsFlat_zero 1 k s]
  dsimp only [tensorFamily]
  erw [reassoc_of% (rightUnitor_naturality (P.composeAheadOfInputs 0 k p))]
  erw [tensorSubstitutionStep_parallel_unit]
  erw [P.composeAheadOfInputs_index_eq 0 k (∑ j, s j) k p (by simp)]

end SerrePositivity.EInfinity.Operad
