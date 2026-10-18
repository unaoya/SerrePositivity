module

public import SerrePositivity.EInfinity.Operad.CompositionBlockDecomposition
public import SerrePositivity.EInfinity.Operad.TensorSubstitutionTransport
public import SerrePositivity.EInfinity.Operad.OneSlotSubstitutionTransport

/-!
# 二ブロック合成の再帰と arity の移送

概要：Berger–Moerdijk §1 の二ブロック分解で、後半の末尾の代入を一段取り出す。
方針：後半の出力の移送を前半の反復合成へ通し、最終出力の移送へまとめる。
規約：前半と後半のブロックの順序を変えない。
使われ方：通常の反復合成と二ブロック合成の一致を後半の長さで帰納する。
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
  composeAfterInputs composeFirstInputs composeFirstInputInsertion tensorSubstitutionStep
  tensorFamilySubstitutionStep

/-- 概要：後半の出力 arity の移送は前半の反復合成の出力へ通せる（Berger–Moerdijk §1）。
方針：代入の最初の射の後合成則と、反復合成の尾の長さの移送を使う。
規約：最初の代入射 f は任意の複体射でよい。
使われ方：後半の再帰の総和の移送を二ブロック合成の末尾へまとめる。 -/
lemma tensorSubstitutionStep_firstInputs_cast (P : Operad A) (n : ℕ) {b c : ℕ}
    (he : b = c) (s : Fin n → ℕ) {R L : Complex A} (f : R ⊗ L ⟶ P.arity (n + b)) :
    tensorSubstitutionStep
      (f ≫ eqToHom (congrArg P.arity (congrArg (n + ·) he))) (P.composeFirstInputs n c s) =
    tensorSubstitutionStep f (P.composeFirstInputs n b s) ≫
      eqToHom (congrArg P.arity (congrArg ((∑ j, s j) + ·) he)) := by
  rw [tensorSubstitutionStep_first_post, P.composeFirstInputs_tail_cast n he s,
    tensorSubstitutionStep_post]

/-- 概要：後半への反復合成の再帰の出力の移送を末尾に分離する（Berger–Moerdijk §1）。
方針：有限族の代入射の後合成則を適用する。
規約：最後の入力の長さは s(last m)。
使われ方：後半の一段の挿入を二ブロックの代入の比較へ接続する。 -/
lemma composeAfterInputs_succ_factor (P : Operad A) (n m k : ℕ) (s : Fin (m + 1) → ℕ) :
    P.composeAfterInputs n (m + 1) k s =
      tensorFamilySubstitutionStep m (fun j => P.arity (s j))
        (P.composeFirstInputInsertion (n + m) k (s (Fin.last m)))
        (P.composeAfterInputs n m (k + s (Fin.last m)) (fun j => s j.castSucc)) ≫
        eqToHom (congrArg P.arity (congrArg (n + ·) (oneSlotComposeOutput_eq m k s))) := by
  conv_lhs => unfold composeAfterInputs
  rw [tensorFamilySubstitutionStep_post]

/-- 概要：二ブロック合成は最後の演算の代入と短い二ブロック合成へ分解できる（Berger–Moerdijk §1）。
方針：後半の出力の移送を前半へ通し、有限族のブロック代入の比較を用いる。
規約：最後の入力の arity を尾へ加えてから再帰する。
使われ方：通常の反復合成と同じ再帰式を満たすことを示す。 -/
lemma composeByBlocks_succ (P : Operad A) (n m k : ℕ) (s : Fin (n + m + 1) → ℕ) :
    P.composeByBlocks n (m + 1) k s =
      tensorFamilySubstitutionStep (n + m) (fun j => P.arity (s j))
        (P.composeFirstInputInsertion (n + m) k (s (Fin.last (n + m))))
        (P.composeByBlocks n m (k + s (Fin.last (n + m))) (fun j => s j.castSucc) ≫
          eqToHom (congrArg P.arity (oneSlotComposeOutput_eq (n + m) k s))) := by
  have hi := oneSlotComposeOutput_eq m k (fun j => s (j.natAdd n))
  have hs := tensorFamily_sum_splitAt n (m + 1) s
  have ht : (∑ j : Fin n, s (j.castAdd (m + 1))) +
      ((∑ j : Fin m, s (j.natAdd n).castSucc) + (k + s (Fin.last (n + m)))) =
      (∑ j, s j) + k := by
    have hi' : (∑ j : Fin m, s (j.natAdd n).castSucc) + (k + s (Fin.last (n + m))) =
        (∑ j : Fin (m + 1), s (j.natAdd n)) + k := hi
    exact (congrArg ((∑ j : Fin n, s (j.castAdd (m + 1))) + ·) hi').trans
      ((Nat.add_assoc (∑ j : Fin n, s (j.castAdd (m + 1)))
        (∑ j : Fin (m + 1), s (j.natAdd n)) k).symm.trans (congrArg (· + k) hs.symm))
  unfold composeByBlocks
  rw [P.composeAfterInputs_succ_factor]
  erw [P.tensorSubstitutionStep_firstInputs_cast n hi
    (fun j => s (j.castAdd (m + 1)))]
  simp only [Category.assoc, eqToHom_trans]
  have h := congrArg (· ≫ eqToHom (congrArg P.arity ht))
    (tensorFamilySubstitutionStep_splitAt n m (fun j => P.arity (s j))
      (P.composeFirstInputInsertion (n + m) k (s (Fin.last (n + m))))
      (P.composeAfterInputs n m (k + s (Fin.last (n + m))) (fun j => s (j.natAdd n).castSucc))
      (P.composeFirstInputs n
        ((∑ j : Fin m, s (j.natAdd n).castSucc) + (k + s (Fin.last (n + m))))
        (fun j => s (j.castAdd (m + 1)))))
  rw [← tensorFamilySubstitutionStep_post] at h
  simp only [Category.assoc] at h
  exact h.symm

end SerrePositivity.EInfinity.Operad
