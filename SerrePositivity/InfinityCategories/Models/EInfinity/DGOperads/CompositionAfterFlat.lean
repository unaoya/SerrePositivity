module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionBlockRecursion
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilySubstitutionParallel

/-!
模型。文献の定義との比較は後で
# 後半への反復合成の出力の括弧付け

概要：Berger–Moerdijk §1 の先頭合成との交換で、後半の反復合成の出力を左括弧でそろえる。
方針：既存の後半への反復合成に arity の結合則の等式の射を後合成する。
規約：出力を n+(∑ s)+k と表し、入力の順序は変えない。
使われ方：先頭の部分合成と後半の有限族への代入の交換則を述べる。
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
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeAfterInputs _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep

/-- 概要：後半への反復合成の出力を左括弧の arity で表す（Berger–Moerdijk §1）。
方針：composeAfterInputs の出力へ加法の結合則の移送を合成する。
規約：前半 n 個、指定入力 m 個、尾 k 個を持つ。
使われ方：先頭への部分合成と後半の代入の出力を同じ arity にそろえる。 -/
def composeAfterInputsFlat (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n m k : ℕ) (s : Fin m → ℕ) :
    P.arity (n + m + k) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s j)) ⟶
      P.arity (n + (∑ j, s j) + k) :=
  P.composeAfterInputs n m k s ≫
    eqToHom (congrArg P.arity (Nat.add_assoc n (∑ j, s j) k).symm)

/-- 概要：左括弧の出力で表した空の後半の反復合成（Berger–Moerdijk §1）。
方針：空の後半の定義を使い、出力の二つの移送をまとめる。
規約：出力は n+(∑ s)+k。
使われ方：平行な反復合成の交換則の空の入力族の場合に使う。 -/
lemma composeAfterInputsFlat_zero (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ) (s : Fin 0 → ℕ) :
    P.composeAfterInputsFlat n 0 k s =
      (ρ_ (P.arity (n + k))).hom ≫ eqToHom (congrArg P.arity
        (by simp : n + k = n + (∑ j, s j) + k)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeAfterInputsFlat
  rw [P.composeAfterInputs_zero, Category.assoc, eqToHom_trans]

/-- 概要：左括弧の出力の反復合成も最後の指定入力から再帰する（Berger–Moerdijk §1）。
方針：後半への反復合成の再帰の式と、有限族の代入の後合成則を用いる。
規約：最後の arity を尾へ加え、総和の移送を再帰の末尾へ置く。
使われ方：平行な代入の有限族の比較へ再帰を適用する。 -/
lemma composeAfterInputsFlat_succ (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n m k : ℕ) (s : Fin (m + 1) → ℕ) :
    P.composeAfterInputsFlat n (m + 1) k s =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep m (fun j => P.arity (s j))
        (P.composeFirstInputInsertion (n + m) k (s (Fin.last m)))
        (P.composeAfterInputsFlat n m (k + s (Fin.last m)) (fun j => s j.castSucc) ≫
          eqToHom (congrArg P.arity (by
            have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq m k s
            omega : n + (∑ j : Fin m, s j.castSucc) + (k + s (Fin.last m)) =
              n + (∑ j, s j) + k))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeAfterInputsFlat
  rw [P.composeAfterInputs_succ_factor]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep_post, eqToHom_trans]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
