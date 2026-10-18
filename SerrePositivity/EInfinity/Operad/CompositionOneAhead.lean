module

public import SerrePositivity.EInfinity.Operad.CompositionBinary
public import SerrePositivity.EInfinity.Operad.CompositionAhead
public import SerrePositivity.EInfinity.Operad.CompositionAfterFlat

/-!
# 一入力への反復合成と先頭合成

概要：Berger–Moerdijk §1 の二ブロック分解で、前半一入力の合成を先頭への部分合成として表す。
方針：一入力の反復合成を部分合成へ簡約し、先頭合成の arity の移送をまとめる。
規約：未代入の尾 k 入力は固定し、一次の有限テンソルの単位因子を除く。
使われ方：後半の合成を済ませた外側の演算へ、内側の合成結果を代入する。
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

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：一入力への反復合成はその単位因子を除いた先頭合成となる（Berger–Moerdijk §1）。
方針：既存の一入力の式と composeAheadOfInputs の定義を比較する。
規約：出力は一入力の arity の総和と尾 k の和へ移す。
使われ方：二ブロック分解の前半一入力を先頭の部分合成に戻す。 -/
lemma composeFirstInputs_one_ahead (P : Operad A) (k : ℕ) (s : Fin 1 → ℕ) :
    P.composeFirstInputs 1 k s =
      (P.arity (1 + k) ◁ (ρ_ (P.arity (s 0))).hom) ≫
        P.composeAheadOfInputs k 0 (s 0) ≫ eqToHom (congrArg P.arity
          (by simp : s 0 + k = (∑ j, s j) + k)) := by
  rw [P.composeFirstInputs_one]
  unfold composeAheadOfInputs
  simp only [Nat.add_zero, Category.assoc, eqToHom_trans]

/-- 概要：尾が空なら後半の反復合成の二つの括弧付けは一致する（Berger–Moerdijk §1）。
方針：零との和の arity の移送を恒等射へ簡約する。
規約：指定入力族の arity は零でもよい。
使われ方：全入力への合成で composeAfterInputs と左括弧の表示を同一視する。 -/
lemma composeAfterInputsFlat_zero_tail (P : Operad A) (n m : ℕ) (s : Fin m → ℕ) :
    P.composeAfterInputsFlat n m 0 s = P.composeAfterInputs n m 0 s := by
  simp only [composeAfterInputsFlat, eqToHom_refl, Category.comp_id]

end SerrePositivity.EInfinity.Operad
