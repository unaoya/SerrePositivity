module

public import SerrePositivity.Spectra.SymmetricSequence.PowerBijectionMonoidal
public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerSingleBlockSwap
public import SerrePositivity.CategoryTheory.Monoidal.BraidingPreservation

/-! # 反復テンソル関手のbraidingの保存と一般のブロック交換

第0段・第1段との交換を基底とし、モノイダル関手のbraidingの保存をテンソル積へ拡張して帰納する。
既存の対称群作用を用いた全次数のブロック交換と連結の両立を証明する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open SerrePositivity.FiniteBijection

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 交換と連結の両立から、braidingの像をtensoratorで比較する。 -/
lemma bijectionFunctor_map_braiding_of_swap (X : C) (m n : ℕ)
    (h : (β_ (power X n) (power X m)).hom ≫ (appendIso X m n).hom ≫
      (bijectionFunctor X).map (sumSymmetry (of m) (of n)).hom = (appendIso X n m).hom) :
    (bijectionFunctor X).map (β_ (of m) (of n)).hom =
      Functor.OplaxMonoidal.δ (bijectionFunctor X) (of m) (of n) ≫
        (β_ ((bijectionFunctor X).obj (of m)) ((bijectionFunctor X).obj (of n))).hom ≫
        Functor.LaxMonoidal.μ (bijectionFunctor X) (of n) (of m) := by
  rw [bijectionFunctor_δ, bijectionFunctor_μ, SymmetricSequence.indexBraiding_eq]
  simp only [bijectionFunctor_obj_of, card_of]
  apply (cancel_epi (appendIso X m n).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply (cancel_epi (β_ (power X n) (power X m)).hom).mp
  simp only [SymmetricCategory.symmetry_assoc]
  exact h
/-- 反復テンソル関手のbraidingの保存。第0段・第1段からテンソル積について帰納する。 -/
lemma bijectionFunctor_map_braiding (X : C) (m n : ℕ) :
    (bijectionFunctor X).map (β_ (of m) (of n)).hom =
      Functor.OplaxMonoidal.δ (bijectionFunctor X) (of m) (of n) ≫
        (β_ ((bijectionFunctor X).obj (of m)) ((bijectionFunctor X).obj (of n))).hom ≫
        Functor.LaxMonoidal.μ (bijectionFunctor X) (of n) (of m) := by
  induction m with
  | zero =>
    apply bijectionFunctor_map_braiding_of_swap
    exact SymmetricSequence.tensorPower_swap_zero_right X n
  | succ m ih =>
    have hx := bijectionFunctor_map_braiding_of_swap X 1 n
      (SymmetricSequence.tensorPower_swap_one_right X n)
    have h := SerrePositivity.MonoidalFunctor.map_braiding_tensor_left
      (bijectionFunctor X) (of 1) (of m) (of n) hx ih
    have he : of 1 ⊗ of m = of (m + 1) := congrArg of (Nat.one_add m)
    rw [he] at h
    exact h
/-- 反復テンソル関手を、既存の置換作用を持つbraidedモノイダル関手として登録する。 -/
instance bijectionFunctorBraided (X : C) : (bijectionFunctor X).Braided where
  toMonoidal := inferInstance
  braided A B := by
    rw [← of_card A, ← of_card B]
    rw [bijectionFunctor_map_braiding]
    simp

end SerrePositivity.TensorPowers

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.TensorPowers SerrePositivity.FiniteBijection

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 全次数のブロック全体の交換と連結の両立。第0段も含む。 -/
lemma tensorPower_block_swap (X : C) (m n : ℕ) :
    (β_ (power X m) (power X n)).hom ≫ (appendIso X n m).hom ≫
        (SymmetricSequence.tensorPowerSequence X).map (sumSymmetry (of n) (of m)).hom =
      (appendIso X m n).hom := by
  have h := Functor.LaxBraided.braided (F := bijectionFunctor X) (of n) (of m)
  simp only [bijectionFunctor_μ, bijectionFunctor_obj_of, SymmetricSequence.indexBraiding_eq,
    card_of] at h
  change (β_ (power X m) (power X n)).hom ≫ (appendIso X n m).hom ≫
    (bijectionFunctor X).map (sumSymmetry (of n) (of m)).hom = _
  rw [h, SymmetricCategory.symmetry_assoc]

end SerrePositivity.SymmetricSequence
