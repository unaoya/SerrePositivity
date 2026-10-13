module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPowerLeftBlock
public import SerrePositivity.CategoryTheory.Monoidal.PermutationAction
public import SerrePositivity.CategoryTheory.FiniteBlockEquiv
public import SerrePositivity.GroupTheory.Coxeter.PermutationInduction

/-! # ブロック置換と反復テンソルの連結

左右の隣接交換の比較を、隣接互換による帰納と既存の作用の乗法則によって全置換へ拡張する。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.Coxeter SerrePositivity.FiniteBijection

/-- 右ブロックの隣接互換の位置の計算。 -/
lemma blockEquiv_adjacent_right (m n : ℕ) (i : Fin n) :
    blockEquiv (1 : Equiv.Perm (Fin m)) (adjacentTransposition i) =
      adjacentTransposition (i.natAdd m) := by
  rw [adjacentTransposition]
  erw [blockEquiv_swap_right]
  rw [adjacentTransposition]
  congr 1

/-- 左ブロックの隣接互換を、次数の移送を介して比較する。 -/
lemma blockEquiv_adjacent_left (m n : ℕ) (i : Fin m) :
    blockEquiv (adjacentTransposition i) (1 : Equiv.Perm (Fin n)) =
      (finCongr (Nat.succ_add m n).symm).permCongr
        (adjacentTransposition (i.castAdd n)) := by
  rw [adjacentTransposition]
  erw [blockEquiv_swap_left]
  change _ = (finCongr (Nat.succ_add m n).symm).symm.trans
    ((Equiv.swap (i.castAdd n).castSucc (i.castAdd n).succ).trans
      (finCongr (Nat.succ_add m n).symm))
  rw [← Equiv.trans_assoc, Equiv.symm_trans_swap_trans]
  congr 1
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 反復テンソルへの置換作用は、次数と置換の移送と両立する。 -/
lemma permutationAction_index_eq (X : C) {r s : ℕ} (h : r = s)
    (σ : Equiv.Perm (Fin r)) :
    eqToHom (congrArg (power X) h) ≫
        (permutationAction X s ((finCongr h).permCongr σ)).asIso.hom =
      (permutationAction X r σ).asIso.hom ≫ eqToHom (congrArg (power X) h) := by
  subst s
  have he : (finCongr (Eq.refl r)).permCongr σ = σ := by
    ext i
    rfl
  simp only [he, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 右ブロックの任意の置換と連結の両立。 -/
lemma appendIso_permutation_right (X : C) (m n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (power X m ◁ (permutationAction X n σ).asIso.hom) ≫ (appendIso X m n).hom =
      (appendIso X m n).hom ≫
        (permutationAction X (m + n) (blockEquiv 1 σ)).asIso.hom := by
  cases n with
  | zero =>
    have hs : σ = 1 := Subsingleton.elim _ _
    subst σ
    simp only [permutationAction_one, whiskerLeft_id, Category.id_comp]
    have hb : blockEquiv (1 : Equiv.Perm (Fin m)) (1 : Equiv.Perm (Fin 0)) = 1 :=
      blockEquiv_refl m 0
    rw [hb, permutationAction_one, Category.comp_id]
  | succ n =>
    apply permutation_induction_right σ
    · rw [permutationAction_one, whiskerLeft_id, Category.id_comp]
      have hb : blockEquiv (1 : Equiv.Perm (Fin m)) (1 : Equiv.Perm (Fin (n + 1))) = 1 :=
        blockEquiv_refl m (n + 1)
      rw [hb, permutationAction_one, Category.comp_id]
    · intro τ i ih
      have hb : blockEquiv (1 : Equiv.Perm (Fin m)) (τ * adjacentTransposition i) =
          blockEquiv 1 τ * blockEquiv 1 (adjacentTransposition i) := by
        simpa only [one_mul] using blockEquiv_mul (1 : Equiv.Perm (Fin m)) 1 τ
          (adjacentTransposition i)
      rw [hb]
      simp only [permutationAction_mul, whiskerLeft_comp, Category.assoc]
      rw [ih, blockEquiv_adjacent_right, permutationAction_adjacent]
      change (power X m ◁ (adjacentIso X n i).hom) ≫ (appendIso X m (n + 1)).hom ≫ _ = _
      rw [← Category.assoc, appendIso_adjacent_right, Category.assoc]
      erw [permutationAction_adjacent]
      rfl

/-- 左ブロックの隣接交換の比較を、全次数の置換作用で読む。 -/
lemma appendIso_adjacent_left_action (X : C) (m n : ℕ) (i : Fin m) :
    ((adjacentIso X m i).hom ▷ power X n) ≫ (appendIso X (m + 1) n).hom =
      (appendIso X (m + 1) n).hom ≫
        (permutationAction X ((m + 1) + n)
          (blockEquiv (adjacentTransposition i) 1)).asIso.hom := by
  rw [blockEquiv_adjacent_left]
  have h := permutationAction_index_eq X (Nat.succ_add m n).symm
    (adjacentTransposition (i.castAdd n))
  rw [permutationAction_adjacent] at h
  change eqToHom _ ≫ _ = (adjacentIso X (m + n) (i.castAdd n)).hom ≫ eqToHom _ at h
  have hh := congrArg (fun f ↦ f ≫ eqToHom (congrArg (power X) (Nat.succ_add m n).symm))
    (appendIso_adjacent_left X m n i)
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at hh
  rw [← h] at hh
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at hh
  exact hh

/-- 左ブロックの任意の置換と連結の両立。 -/
lemma appendIso_permutation_left (X : C) (m n : ℕ) (σ : Equiv.Perm (Fin m)) :
    ((permutationAction X m σ).asIso.hom ▷ power X n) ≫ (appendIso X m n).hom =
      (appendIso X m n).hom ≫
        (permutationAction X (m + n) (blockEquiv σ 1)).asIso.hom := by
  cases m with
  | zero =>
    have hs : σ = 1 := Subsingleton.elim _ _
    subst σ
    rw [permutationAction_one, id_whiskerRight, Category.id_comp]
    have hb : blockEquiv (1 : Equiv.Perm (Fin 0)) (1 : Equiv.Perm (Fin n)) = 1 :=
      blockEquiv_refl 0 n
    rw [hb, permutationAction_one, Category.comp_id]
  | succ m =>
    apply permutation_induction_right σ
    · rw [permutationAction_one, id_whiskerRight, Category.id_comp]
      have hb : blockEquiv (1 : Equiv.Perm (Fin (m + 1))) (1 : Equiv.Perm (Fin n)) = 1 :=
        blockEquiv_refl (m + 1) n
      rw [hb, permutationAction_one, Category.comp_id]
    · intro τ i ih
      have hb : blockEquiv (τ * adjacentTransposition i) (1 : Equiv.Perm (Fin n)) =
          blockEquiv τ 1 * blockEquiv (adjacentTransposition i) 1 := by
        simpa only [one_mul] using blockEquiv_mul τ (adjacentTransposition i)
          (1 : Equiv.Perm (Fin n)) 1
      rw [hb]
      simp only [permutationAction_mul, comp_whiskerRight, Category.assoc]
      rw [ih, permutationAction_adjacent]
      change ((adjacentIso X m i).hom ▷ power X n) ≫ (appendIso X (m + 1) n).hom ≫ _ = _
      rw [← Category.assoc, appendIso_adjacent_left_action, Category.assoc]

/-- 左右の任意の置換と連結の両立。第0段も含む。 -/
lemma appendIso_block_permutation (X : C) (m n : ℕ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    ((permutationAction X m σ).asIso.hom ⊗ₘ (permutationAction X n τ).asIso.hom) ≫
        (appendIso X m n).hom =
      (appendIso X m n).hom ≫
        (permutationAction X (m + n) (blockEquiv σ τ)).asIso.hom := by
  have hb : blockEquiv σ τ = blockEquiv 1 τ * blockEquiv σ 1 := by
    simpa only [one_mul, mul_one] using blockEquiv_mul (1 : Equiv.Perm (Fin m)) σ τ 1
  rw [hb, permutationAction_mul]
  simp only [tensorHom_def, Category.assoc]
  rw [appendIso_permutation_right]
  rw [← Category.assoc, appendIso_permutation_left, Category.assoc]

end SerrePositivity.TensorPowers
