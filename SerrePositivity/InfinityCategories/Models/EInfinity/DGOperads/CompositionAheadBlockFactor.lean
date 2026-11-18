module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAheadNested
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAheadParallel
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionBlockTheorem
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionOneAhead
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionFirstNested

/-!
模型。文献の定義との比較は後で
# 先頭への部分合成の後の全入力への代入

概要：Berger–Moerdijk §1 の部分合成と全合成の結合を二ブロックの式で表す。
方針：後半への代入との平行な交換則と、内側の全入力への代入の結合則を接続する。
規約：内側の n 入力を前半、外側の残る m 入力を後半とする。
使われ方：自由代数の部分合成則の係数側を全合成の先頭分解へ接続する。
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

/-- 概要：未代入の尾が空の先頭合成は内側の全合成と結合する（Berger–Moerdijk §1）。
方針：一般の入れ子の結合則で尾の長さを零とし、恒等な移送を除く。
規約：残る外側の m 入力は内側の入力より後に置く。
使われ方：二ブロック分解の前半の合成を内側の全合成へ移す。 -/
lemma composeAheadOfInputs_nested_zero (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n : ℕ) (s : Fin n → ℕ) :
    (P.composeAheadOfInputs m 0 n ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j))) ≫
      P.composeFirstInputs n m s =
    (α_ (P.arity (1 + m)) (P.arity n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j)))).hom ≫
      (P.arity (1 + m) ◁ P.composition n s) ≫
        P.composeAheadOfInputs m 0 (∑ j, s j) := by
  simpa only [Nat.add_zero, eqToHom_refl, id_whiskerRight, Category.id_comp,
    Category.comp_id] using P.composeAheadOfInputs_nested m 0 n s

/-- 概要：先頭の部分合成と二ブロックの代入は内側の全合成を通して計算できる（Berger–Moerdijk §1）。
方針：後半への代入との交換則と前半の入れ子の結合則をテンソル代入の一般補題で結合する。
規約：前半の演算族 s、後半の演算族 t は空の族と arity 零を許す。
使われ方：先頭への部分合成後の全合成を、外側の全合成の先頭分解へ変形する。 -/
lemma composeAheadOfInputs_substitution_blocks (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n : ℕ)
    (s : Fin n → ℕ) (t : Fin m → ℕ) :
    (P.composeAheadOfInputs m 0 n ▷
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j)) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (t j)))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeAfterInputsFlat n m 0 t)
        (P.composeFirstInputs n (∑ j, t j) s) =
    (α_ (P.arity (1 + m)) (P.arity n)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j)) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (t j)))).hom ≫
      (P.arity (1 + m) ◁ (α_ (P.arity n)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j)))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (t j)))).inv) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeAfterInputsFlat 1 m 0 t)
        ((P.arity (1 + ∑ j, t j) ◁ P.composition n s) ≫
          P.composeAheadOfInputs (∑ j, t j) 0 (∑ j, s j)) := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_first_nested
    (P.composeAheadOfInputs m 0 n) (P.composeAfterInputsFlat n m 0 t)
    (P.composeAfterInputsFlat 1 m 0 t) (P.composeAheadOfInputs (∑ j, t j) 0 n)
    (P.composeFirstInputs n (∑ j, t j) s) (P.composition n s)
    (P.composeAheadOfInputs (∑ j, t j) 0 (∑ j, s j))
    (P.composeAheadOfInputs_after_parallel m 0 n t)
    (P.composeAheadOfInputs_nested_zero (∑ j, t j) n s)

/-- 概要：先頭へ部分合成した後の全合成は、後半の代入と内側の全合成で計算できる（Berger–Moerdijk §1）。
方針：全合成を二ブロックへ分解し、平行な交換則と入れ子の結合則を適用する。
規約：s の前半 n 個が内側、後半 m 個が外側の残る入力に対応する。
使われ方：Schur 作用の先頭での部分合成則の係数射を比較する。 -/
lemma composition_after_first_blocks (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n : ℕ) (s : Fin (n + m) → ℕ) :
    (P.composeAheadOfInputs m 0 n ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => P.arity (s j))) ≫
      P.composition (n + m) s =
    ((P.arity (1 + m) ⊗ P.arity n) ◁
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m (fun j => P.arity (s j))).hom) ≫
    (α_ (P.arity (1 + m)) (P.arity n)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s (j.castAdd m))) ⊗
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s (j.natAdd n))))).hom ≫
      (P.arity (1 + m) ◁ (α_ (P.arity n)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s (j.castAdd m))))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => P.arity (s (j.natAdd n))))).inv) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeAfterInputsFlat 1 m 0 (fun j => s (j.natAdd n)))
        ((P.arity (1 + ∑ j : Fin m, s (j.natAdd n)) ◁
          P.composition n (fun j => s (j.castAdd m))) ≫
          P.composeAheadOfInputs (∑ j : Fin m, s (j.natAdd n)) 0
            (∑ j : Fin n, s (j.castAdd m))) ≫
      eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_splitAt n m s).symm) := by
  rw [P.composition_eq_blocks n m s]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeByBlocks
  rw [← whisker_exchange_assoc]
  rw [← P.composeAfterInputsFlat_zero_tail n m (fun j => s (j.natAdd n))]
  erw [reassoc_of% (P.composeAheadOfInputs_substitution_blocks m n
    (fun j => s (j.castAdd m)) (fun j => s (j.natAdd n)))]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
