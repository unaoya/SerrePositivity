module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionBlockRecursion

/-!
模型。文献の定義との比較は後で
# 反復合成の二ブロックへの分解

概要：Berger–Moerdijk §1 の全入力への反復合成を二つの連続した入力ブロックで計算する。
方針：後半の長さで帰納し、両方の合成射の同じ末尾からの再帰式を比較する。
規約：後半を先に、前半を後に代入し、未代入の尾 k 入力を保つ。
使われ方：Schur 作用の部分合成則で入力族を二ブロックに分ける。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeAfterInputs _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeByBlocks

/-- 概要：任意の長さの反復合成は後半と前半の二ブロックの合成に一致する（Berger–Moerdijk §1）。
方針：後半の長さで帰納し、最後の演算の代入を取り出して帰納仮定を使う。
規約：空の前半、空の後半、arity 0 の演算を含む。
使われ方：自由代数の部分合成則で全入力への合成をブロックごとの合成へ移す。 -/
lemma composeFirstInputs_eq_blocks (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n m k : ℕ) (s : Fin (n + m) → ℕ) :
    P.composeFirstInputs (n + m) k s = P.composeByBlocks n m k s := by
  induction m generalizing k with
  | zero => exact (P.composeByBlocks_zero n k s).symm
  | succ m ih =>
    rw [P.composeByBlocks_succ n m k s,
      ← ih (k + s (Fin.last (n + m))) (fun j => s j.castSucc)]
    erw [P.composeFirstInputs_succ_factor (n + m) k s]
    rfl

/-- 概要：全入力への合成は任意の二つの連続した入力ブロックで計算できる（Berger–Moerdijk §1）。
方針：未代入の尾を零個として反復合成のブロック分解を適用する。
規約：外側の arity は n+m、入力族を前半 n 個と後半 m 個へ分ける。
使われ方：Schur 演算の生成射を部分合成に対応する入力ブロックへ分解する。 -/
lemma composition_eq_blocks (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n m : ℕ) (s : Fin (n + m) → ℕ) :
    P.composition (n + m) s = P.composeByBlocks n m 0 s := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composition, eqToHom_refl, id_whiskerRight, Category.id_comp, Category.comp_id]
    using P.composeFirstInputs_eq_blocks n m 0 s

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
