module

public import SerrePositivity.EInfinity.Operad.CompositionAdjacentRecursion

/-!
# 反復合成の任意の隣接交換に関する外側等変性

概要：Berger–Moerdijk §1 の反復合成が、指定入力の任意の隣接二位置の交換と両立することを示す。
方針：交換位置が末尾なら二位置への合成の交換則を使い、それ以外は最後の入力を代入して帰納する。
規約：未代入の尾 k 個の内部の順序を保つ。
使われ方：全入力への合成と Schur 対象の作用の外側等変性へ適用する。
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
  composeFirstInputs arityBijectionMap

/-- 概要：前方への反復合成は任意の隣接交換を出力の全単射へ移す（Berger–Moerdijk §1）。
方針：指定入力数で帰納し、末尾二入力の交換と末尾固定の交換の帰納段階を使う。
規約：n+1 個の指定入力の隣接位置 i を交換し、未代入入力 k 個は保つ。
使われ方：全入力への合成の外側等変性を隣接互換による生成から証明する。 -/
lemma composeFirstInputs_adjacent_equivariance (P : Operad A) (n k : ℕ)
    (s : Fin (n + 1) → ℕ) (i : Fin n) :
    (P.sequence.map (FiniteBijection.permutation (n + 1 + k)
        (FiniteBijection.blockEquiv (adjacentTransposition i) (Equiv.refl (Fin k)))) ⊗ₘ
      (tensorFamilyAdjacentIso n (fun j => P.arity (s j)) i).hom) ≫
        P.composeFirstInputs (n + 1) k (fun j => s (adjacentTransposition i j)) =
      P.composeFirstInputs (n + 1) k s ≫
        P.arityBijectionMap (operadCompositionAdjacentOutput n k s i) := by
  induction n generalizing k with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [operadCompositionAdjacentOutput_last, operadLastTwoInputSwap_block]
      exact P.composeFirstInputs_lastSwap_equivariance n k s
    · rw [operadCompositionAdjacentOutput_castSucc]
      exact P.composeFirstInputs_adjacent_cast_equivariance n k s i
        (operadCompositionAdjacentOutput n (k + s (Fin.last (n + 1))) (fun j => s j.castSucc) i)
        (ih (k + s (Fin.last (n + 1))) (fun j => s j.castSucc) i)

/-- 概要：全入力への合成は未代入入力が零個の前方への反復合成に一致する（Berger–Moerdijk §1）。
方針：零との和の arity の移送を恒等射として簡約する。
規約：始域と終域の零との和は定義的に同一視する。
使われ方：反復合成の等変性を全入力への合成へ適用する。 -/
lemma composition_eq_composeFirstInputs_zero (P : Operad A) (n : ℕ) (s : Fin n → ℕ) :
    P.composition n s = P.composeFirstInputs n 0 s := by
  simp only [composition, eqToHom_refl, id_whiskerRight, Category.id_comp, Category.comp_id]

/-- 概要：全入力への合成は任意の隣接交換を出力の全単射へ移す（Berger–Moerdijk §1）。
方針：未代入の尾を零個として反復合成の隣接交換の等変性を適用する。
規約：外側の arity は n+1、内側の入力族の各因子は独立の複体。
使われ方：Schur 対象の作用の外側等変性を生成する隣接交換について証明する。 -/
lemma composition_adjacent_equivariance (P : Operad A) (n : ℕ)
    (s : Fin (n + 1) → ℕ) (i : Fin n) :
    (P.sequence.map (FiniteBijection.permutation (n + 1) (adjacentTransposition i)) ⊗ₘ
      (tensorFamilyAdjacentIso n (fun j => P.arity (s j)) i).hom) ≫
        P.composition (n + 1) (fun j => s (adjacentTransposition i j)) =
      P.composition (n + 1) s ≫
        P.arityBijectionMap (operadCompositionAdjacentOutput n 0 s i) := by
  have h := P.composeFirstInputs_adjacent_equivariance n 0 s i
  have hp : FiniteBijection.blockEquiv (adjacentTransposition i) (Equiv.refl (Fin 0)) =
      adjacentTransposition i := by
    rw [blockEquiv_zero_right]
    apply Equiv.ext
    intro x
    rfl
  rw [hp] at h
  simpa only [composition_eq_composeFirstInputs_zero] using h

end SerrePositivity.EInfinity.Operad
