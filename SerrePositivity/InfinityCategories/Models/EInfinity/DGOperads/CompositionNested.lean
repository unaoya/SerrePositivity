module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionNestedRecursion

/-!
模型。文献の定義との比較は後で
# 先頭入力への合成と任意の長さの反復合成

概要：Berger–Moerdijk §1 の入れ子の部分合成を任意の有限入力族の代入と両立させる。
方針：空の入力族を基底とし、最後の演算の代入と残りの演算の帰納仮定を接続する。
規約：外側の先頭入力へ合成し、内側の先頭 n 入力へ代入して尾 k 個を残す。
使われ方：Schur 作用の部分合成との両立を生成射上で証明する。
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

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputInsertion _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeIntoFirst _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep

/-- 概要：内側の指定入力への反復合成と外側の先頭入力への合成は結合的である（Berger–Moerdijk §1）。
方針：入力数で帰納し、最後の入力の入れ子の挿入と前半の結合則を有限族の代入の比較へ適用する。
規約：arity 0 の演算を許し、各ブロックと未代入の尾の順序を保つ。
使われ方：自由代数の作用の部分合成則を構成するための係数側の結合則となる。 -/
lemma composeIntoFirst_nested (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n k : ℕ) (s : Fin n → ℕ) :
    (P.composeIntoFirst m n k ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j))) ≫
      P.composeFirstInputs n (m + k) s =
    (α_ (P.arity (m + 1)) (P.arity (n + k)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j)))).hom ≫
      (P.arity (m + 1) ◁ P.composeFirstInputs n k s) ≫
        P.composeIntoFirst m (∑ j, s j) k := by
  induction n generalizing k with
  | zero => exact P.composeIntoFirst_nested_zero m k s
  | succ n ih =>
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep_nested n (fun j => P.arity (s j))
      (P.composeIntoFirst m (n + 1) k)
      (P.composeFirstInputInsertion n k (s (Fin.last n)))
      (P.composeFirstInputInsertion n (m + k) (s (Fin.last n)))
      (P.composeIntoFirst m n (k + s (Fin.last n)) ≫ eqToHom (congrArg P.arity
        (by omega : n + (m + (k + s (Fin.last n))) = n + ((m + k) + s (Fin.last n)))))
      (P.composeFirstInputs n ((m + k) + s (Fin.last n)) (fun j => s j.castSucc) ≫
        eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq n (m + k) s)))
      (P.composeFirstInputs n (k + s (Fin.last n)) (fun j => s j.castSucc) ≫
        eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq n k s)))
      (P.composeIntoFirst m (∑ j, s j) k)
      (P.composeIntoFirst_insertion_raw m n k (s (Fin.last n)))
      (P.composeIntoFirst_prefix_nested m n k s
        (ih (k + s (Fin.last n)) (fun j => s j.castSucc)))
    rw [P.composeFirstInputs_succ_factor n (m + k) s, P.composeFirstInputs_succ_factor n k s]
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputInsertion] using h

/-- 概要：内側の全入力への合成は外側の先頭入力への部分合成と結合的である（Berger–Moerdijk §1）。
方針：未代入の内側の尾を零個として一般の入れ子の反復合成を適用する。
規約：外側の残り m 入力は未代入で保ち、出力を (∑ s)+m で表す。
使われ方：Schur 作用の部分合成則で内側の全入力をまとめる。 -/
lemma composition_nested_first (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n : ℕ) (s : Fin n → ℕ) :
    (P.comp m n 0 ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j))) ≫
      (eqToHom (congrArg P.arity (Nat.add_comm m n)) ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j))) ≫
      P.composeFirstInputs n m s =
    (α_ (P.arity (m + 1)) (P.arity n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j)))).hom ≫
      (P.arity (m + 1) ◁ P.composition n s) ≫ P.comp m (∑ j, s j) 0 ≫
        eqToHom (congrArg P.arity (Nat.add_comm m (∑ j, s j))) := by
  have h := P.composeIntoFirst_nested m n 0 s
  simpa only [Nat.add_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeIntoFirst, comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composition, eqToHom_refl,
    id_whiskerRight, Category.id_comp, Category.comp_id, Category.assoc] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
