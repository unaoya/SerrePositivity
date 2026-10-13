module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPowerBlockGenerators

/-!
# 左ブロックの隣接交換と反復テンソルの連結

先頭二因子の交換を尾の連結と比較し、交換位置についての帰納で左ブロック全体へ拡張する。
右ブロックの比較と同じ既存の隣接交換を用い、次数の移送を明示する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [SymmetricCategory C] in
/-- 二因子を保った尾の連結を、二因子を一つのブロックとする形へ括り直す。 -/
@[reassoc] lemma prefix_pair_factor (X A B D : C) (f : A ⊗ B ⟶ D) :
    (α_ X (X ⊗ A) B).hom ≫ (X ◁ (α_ X A B).hom) ≫ (X ◁ X ◁ f) =
      ((α_ X X A).inv ▷ B) ≫ (α_ (X ⊗ X) A B).hom ≫
        ((X ⊗ X) ◁ f) ≫ (α_ X X D).hom := by
  rw [associator_naturality_right]
  rw [pentagon_inv_hom_hom_hom_hom_assoc]

/-- 二因子の交換は、任意の射による尾の連結と両立する。 -/
lemma prefix_pair_swap (X A B D : C) (f : A ⊗ B ⟶ D) :
    (((α_ X X A).inv ≫ ((β_ X X).hom ▷ A) ≫ (α_ X X A).hom) ▷ B) ≫
        (α_ X (X ⊗ A) B).hom ≫ (X ◁ (α_ X A B).hom) ≫ (X ◁ X ◁ f) =
      (α_ X (X ⊗ A) B).hom ≫ (X ◁ (α_ X A B).hom) ≫ (X ◁ X ◁ f) ≫
        (α_ X X D).inv ≫ ((β_ X X).hom ▷ D) ≫ (α_ X X D).hom := by
  rw [prefix_pair_factor X A B D f, prefix_pair_factor_assoc X A B D f]
  simp only [comp_whiskerRight, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc (α_ X X A).hom (α_ X X A).inv,
    Iso.hom_inv_id, id_whiskerRight, Category.id_comp]
  rw [associator_naturality_left_assoc, whisker_exchange_assoc]
omit [SymmetricCategory C] in
/-- 先頭二因子を保つ連結の展開。自然数の次数の移送も明示する。 -/
lemma appendIso_two_prefix (X : C) (m n : ℕ) :
    (appendIso X (m + 2) n).hom =
      (α_ X (X ⊗ power X m) (power X n)).hom ≫
        (X ◁ (α_ X (power X m) (power X n)).hom) ≫
        (X ◁ X ◁ (appendIso X m n).hom) ≫
        eqToHom (congrArg (power X) (by omega : (m + n) + 2 = (m + 2) + n)) := by
  simp only [appendIso, Iso.trans_hom, whiskerLeftIso_hom, eqToIso.hom,
    whiskerLeft_comp, Category.assoc, whiskerLeft_eqToHom, eqToHom_trans]
  rfl

/-- 左ブロックの先頭二因子の交換と連結の両立。 -/
lemma appendIso_swapFirst (X : C) (m n : ℕ) :
    ((swapFirstIso X m).hom ▷ power X n) ≫ (appendIso X (m + 2) n).hom ≫
        eqToHom (congrArg (power X) (by omega : (m + 2) + n = (m + n) + 2)) =
      (appendIso X (m + 2) n).hom ≫
        eqToHom (congrArg (power X) (by omega : (m + 2) + n = (m + n) + 2)) ≫
        (swapFirstIso X (m + n)).hom := by
  rw [appendIso_two_prefix]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  simpa only [swapFirstIso, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom] using
    prefix_pair_swap X (power X m) (power X n) (power X (m + n))
      (appendIso X m n).hom

omit [SymmetricCategory C] in
/-- 左ブロックに一因子を加えた連結から、後続次数の移送を取り除く。 -/
@[reassoc] lemma appendIso_succ_left_normalized (X : C) (m n : ℕ) :
    (appendIso X (m + 1) n).hom ≫
        eqToHom (congrArg (power X) (Nat.succ_add m n)) =
      (α_ X (power X m) (power X n)).hom ≫ X ◁ (appendIso X m n).hom := by
  simp only [appendIso, Iso.trans_hom, whiskerLeftIso_hom, eqToIso.hom,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- 左ブロックの後続位置の交換と次数の移送の比較。 -/
lemma adjacentIso_castAdd_succ (X : C) (m n : ℕ) (i : Fin m) :
    (X ◁ eqToHom (congrArg (power X) (Nat.succ_add m n))) ≫
        (X ◁ (adjacentIso X (m + n) (i.castAdd n)).hom) =
      (adjacentIso X ((m + 1) + n) (i.succ.castAdd n)).hom ≫
        (X ◁ eqToHom (congrArg (power X) (Nat.succ_add m n))) := by
  have hi : Fin.cast (Nat.succ_add m n) (i.succ.castAdd n) =
      (i.castAdd n).succ := by
    apply Fin.ext
    rfl
  have h := adjacentIso_index_eq X (Nat.succ_add m n) (i.succ.castAdd n)
  rw [hi] at h
  erw [power_index_succ X (Nat.succ_add m n)] at h
  simpa only [adjacentIso, Fin.cases_succ, whiskerLeftIso_hom] using h

/-- 左ブロックの隣接交換は、連結後の同じ位置の交換へ送られる。 -/
lemma appendIso_adjacent_left (X : C) (m n : ℕ) (i : Fin m) :
    ((adjacentIso X m i).hom ▷ power X n) ≫ (appendIso X (m + 1) n).hom ≫
        eqToHom (congrArg (power X) (Nat.succ_add m n)) =
      (appendIso X (m + 1) n).hom ≫
        eqToHom (congrArg (power X) (Nat.succ_add m n)) ≫
        (adjacentIso X (m + n) (i.castAdd n)).hom := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [adjacentIso, Fin.cases_zero]
      have hh := adjacentIso_index_eq X (Nat.succ_add m n)
        ((0 : Fin (m + 1)).castAdd n)
      have hi : Fin.cast (Nat.succ_add m n) ((0 : Fin (m + 1)).castAdd n) =
          (0 : Fin ((m + n) + 1)) := by
        apply Fin.ext
        rfl
      rw [hi] at hh
      simp only [adjacentIso, Fin.cases_zero] at hh
      have h := congrArg (fun f ↦ f ≫ eqToHom (congrArg (power X)
        (congrArg (· + 1) (Nat.succ_add m n).symm))) (appendIso_swapFirst X m n)
      simp only [Category.assoc] at h
      have hh' := congrArg (fun f ↦ f ≫ eqToHom (congrArg (power X)
        (congrArg (· + 1) (Nat.succ_add m n).symm))) hh
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at hh'
      have ht : eqToHom (congrArg (power X)
          (by omega : (m + 2) + n = (m + n) + 2)) =
          eqToHom (congrArg (power X) (Nat.succ_add (m + 1) n)) ≫
            eqToHom (congrArg (power X) (congrArg (· + 1) (Nat.succ_add m n))) := by
        rw [eqToHom_trans]
      rw [ht] at h
      simp only [Category.assoc] at h
      rw [hh'] at h
      simp only [eqToHom_trans] at h
      exact h
    · rw [appendIso_succ_left_normalized]
      simp only [adjacentIso, Fin.cases_succ, whiskerLeftIso_hom]
      rw [associator_naturality_middle_assoc]
      rw [appendIso_succ_left_normalized_assoc]
      apply (cancel_mono (X ◁ eqToHom (congrArg (power X) (Nat.succ_add m n)))).mp
      simp only [Category.assoc]
      erw [← adjacentIso_castAdd_succ X m n j]
      simp only [← whiskerLeft_comp]
      rw [ih j]

end SerrePositivity.TensorPowers
