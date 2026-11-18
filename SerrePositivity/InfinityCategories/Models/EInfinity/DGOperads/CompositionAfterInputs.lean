module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IteratedCompositionEquivariance
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionUnit

/-!
模型。文献の定義との比較は後で
# 前方の入力を残した後半への反復合成

概要：Berger–Moerdijk §1 の部分合成則で、前半を残して後半の演算族を合成する。
方針：後半の最後の指定入力から代入し、残りの族へ再帰する。
規約：前半 n 入力と未代入の尾 k 入力の順序を保つ。
使われ方：全入力への合成を二つの連続した入力ブロックに分解する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：前方 n 入力を残し、続く m 入力へ演算を代入する（Berger–Moerdijk §1）。
方針：m の末尾の入力の演算を先に代入し、更新した尾へ再帰する。
規約：出力 arity は n+((∑ s)+k)。演算の係数の移動は Koszul 対称性を使う。
使われ方：反復合成を後半の合成と前半の合成へ分解する際の後半の射となる。 -/
def composeAfterInputs (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n : ℕ) : ∀ (m k : ℕ) (s : Fin m → ℕ),
    P.arity (n + m + k) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s j)) ⟶
      P.arity (n + ((∑ j, s j) + k))
  | 0, k, s =>
    (ρ_ (P.arity (n + k))).hom ≫ eqToHom (congrArg P.arity (by simp))
  | m + 1, k, s =>
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep m (fun j => P.arity (s j))
      (P.composeFirstInputInsertion (n + m) k (s (Fin.last m)))
      (P.composeAfterInputs n m (k + s (Fin.last m)) (fun j => s j.castSucc) ≫
        eqToHom (congrArg P.arity (by
          rw [Fin.sum_univ_castSucc s]
          omega : n + ((∑ j : Fin m, s j.castSucc) + (k + s (Fin.last m))) =
            n + ((∑ j, s j) + k))))

/-- 概要：後半の指定入力が空の反復合成は右単位子と arity の移送となる（Berger–Moerdijk §1）。
方針：再帰の基底を評価する。
規約：前半 n 入力と尾 k 入力だけを残す。
使われ方：二ブロックへの合成の分解の帰納法の基底を処理する。 -/
lemma composeAfterInputs_zero (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ) (s : Fin 0 → ℕ) :
    P.composeAfterInputs n 0 k s =
      (ρ_ (P.arity (n + k))).hom ≫ eqToHom (congrArg P.arity
        (by simp : n + k = n + ((∑ j, s j) + k))) := rfl

/-- 概要：後半一入力への反復合成は通常の一段の挿入となる（Berger–Moerdijk §1）。
方針：空の残りの族の単位子を除き、出力の arity の移送をまとめる。
規約：代入位置は前方 n 入力の直後。
使われ方：二ブロックの分解の一入力の場合を既存の部分合成へ接続する。 -/
lemma composeAfterInputs_one (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ) (s : Fin 1 → ℕ) :
    P.composeAfterInputs n 1 k s =
      (P.arity (n + 1 + k) ◁ (ρ_ (P.arity (s 0))).hom) ≫
        P.composeFirstInputInsertion n k (s 0) ≫ eqToHom (congrArg P.arity
          (by simp; omega : n + (k + s 0) = n + ((∑ j, s j) + k))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeAfterInputs]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeAfterInputs, Category.assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep_zero_post]
  rw [eqToHom_trans]
  rfl

/-- 概要：後半への反復合成は尾の長さの等式の移送と両立する（Berger–Moerdijk §1）。
方針：尾の長さを等式で同一視する。
規約：前半の長さと後半の入力族を固定する。
使われ方：二ブロックの合成の再帰で更新した尾の括弧付けをそろえる。 -/
@[reassoc]
lemma composeAfterInputs_tail_cast (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n m : ℕ) {k l : ℕ} (h : k = l)
    (s : Fin m → ℕ) :
    (eqToHom (congrArg P.arity (congrArg (n + m + ·) h)) ▷
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s j))) ≫ P.composeAfterInputs n m l s =
    P.composeAfterInputs n m k s ≫
      eqToHom (congrArg P.arity (congrArg (fun q => n + ((∑ j, s j) + q)) h)) := by
  subst l
  simp only [eqToHom_refl, id_whiskerRight, Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
