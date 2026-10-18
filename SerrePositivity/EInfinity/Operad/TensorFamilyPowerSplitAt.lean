module

public import SerrePositivity.EInfinity.Operad.TensorFamilyPowerSplitLast
public import SerrePositivity.EInfinity.Operad.TensorFamilySplitAt
public import SerrePositivity.EInfinity.Operad.TensorFamilyBlockSum

/-!
# テンソル冪の連結と二ブロックへの分離

概要：Berger–Moerdijk §1 の全合成の入力側を二ブロックに分けて計算する。
方針：後半の長さで帰納し、末尾の再結合と連結の両立を使う。
規約：前半と後半の順序を保ち、空のブロックと零乗の因子を許す。
使われ方：自由代数の部分合成則の入力の連結を比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：二ブロックを別々に連結してから連結すると全体の連結に等しい（Berger–Moerdijk §1）。
方針：後半の最後の一因子を分離し、帰納仮定と連結の結合則を使う。
規約：総 arity は元の有限族の和に戻す。
使われ方：内側と外側の二段の演算の入力を全入力の連結へ比較する。 -/
lemma tensorPowerFamilyIso_splitAt (K : Complex A) (n m : ℕ) (s : Fin (n + m) → ℕ) :
    (tensorFamilySplitAt n m (fun j => power K (s j))).hom ≫
      ((tensorPowerFamilyIso K n (fun j => s (j.castAdd m))).hom ⊗ₘ
        (tensorPowerFamilyIso K m (fun j => s (j.natAdd n))).hom) ≫
      (appendIso K (∑ j : Fin n, s (j.castAdd m)) (∑ j : Fin m, s (j.natAdd n))).hom ≫
      eqToHom (congrArg (power K) (tensorFamily_sum_splitAt n m s).symm) =
    (tensorPowerFamilyIso K (n + m) s).hom := by
  induction m with
  | zero =>
    simp only [tensorFamilySplitAt, Iso.symm_hom]
    erw [rightUnitor_inv_comp_tensorHom_assoc]
    rw [tensorPowerFamilyIso]
    simp only [eqToIso.hom]
    erw [appendIso_index_right_assoc K (∑ j : Fin n, s (j.castAdd 0))
      (Fin.sum_univ_zero (fun j : Fin 0 => s (j.natAdd n))).symm]
    rw [appendIso_zero_right]
    simp only [Iso.inv_hom_id_assoc, eqToHom_trans]
    rfl
  | succ m ih =>
    simp only [tensorFamilySplitAt, Iso.trans_hom, whiskerRightIso_hom,
      whiskerLeftIso_hom, Iso.symm_hom, Category.assoc]
    rw [whiskerLeft_comp_tensorHom_assoc]
    erw [tensorPowerFamilyIso_splitLast_inv K m (fun j => s (j.natAdd n))]
    rw [← tensorHom_comp_whiskerLeft]
    simp only [whiskerLeft_comp, Category.assoc]
    erw [← associator_naturality_assoc]
    erw [appendIso_index_right_assoc K (∑ j : Fin n, s (j.castAdd (m + 1)))
      (Fin.sum_univ_castSucc (fun j : Fin (m + 1) => s (j.natAdd n))).symm]
    simp only [eqToHom_trans]
    erw [← reassoc_of% (appendIso_associativity K
      (∑ j : Fin n, s (j.castAdd (m + 1)))
      (∑ j : Fin m, s (j.natAdd n).castSucc) (s (Fin.last (n + m))))]
    simp only [eqToHom_trans]
    erw [tensorHom_id]
    erw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
    have hi := congrArg (· ≫ eqToHom (congrArg (power K)
      (tensorFamily_sum_splitAt n m (fun j => s j.castSucc))))
      (ih (fun j => s j.castSucc))
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at hi
    simp only [Category.assoc]
    erw [hi]
    simp only [comp_whiskerRight, Category.assoc]
    erw [appendIso_index_left_assoc K
      (tensorFamily_sum_splitAt n m (fun j => s j.castSucc))]
    simp only [eqToHom_trans]
    have hl := congrArg (· ≫ eqToHom (congrArg (power K) (Fin.sum_univ_castSucc s).symm))
      (tensorPowerFamilyIso_splitLast K (n + m) s)
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      tensorHom_id] at hl
    exact hl.symm

end SerrePositivity.EInfinity
