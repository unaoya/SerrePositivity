module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Permutation
public import SerrePositivity.CategoryTheory.Limits
public import SerrePositivity.GroupTheory.Coxeter.PermutationInduction
public import SerrePositivity.GroupTheory.Coxeter.FirstToLast

/-!
# Monoidal.TensorPower.Blocks

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Monoidal.TensorPower.Blocks` を直接 import する。
-/

/-! ## TensorPowerBlockGenerators（旧 SerrePositivity/CategoryTheory/Monoidal/TensorPowerBlockGenerators.lean） -/

/-!
# 次数の連結とブロック内の隣接交換

次数の移送と隣接交換を比較し、連結同型を介したブロック置換への接続を整える。
-/

@[expose] public section TensorPowerBlockGenerators
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 隣接交換は次数とその有限添字の移送と両立する。 -/
@[reassoc] lemma adjacentIso_index_eq (X : C) {r s : ℕ} (h : r = s) (i : Fin r) :
    eqToHom (congrArg (power X) (congrArg (· + 1) h)) ≫
        (adjacentIso X s (Fin.cast h i)).hom =
      (adjacentIso X r i).hom ≫ eqToHom (congrArg (power X) (congrArg (· + 1) h)) := by
  subst s
  simp

/-- 一因子を加えた後の右ブロックの位置の計算。 -/
lemma natAdd_succ_cast (m n : ℕ) (i : Fin n) :
    Fin.cast (Nat.succ_add m n).symm (i.natAdd m).succ = i.natAdd (m + 1) := by
  apply Fin.ext
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- 左に空のブロックを置くときの有限添字の移送。 -/
lemma natAdd_zero_cast (n : ℕ) (i : Fin n) :
    Fin.cast (Nat.zero_add n).symm i = i.natAdd 0 := by
  apply Fin.ext
  simp

/-- 右ブロックの隣接交換は、連結後の対応する位置の交換へ送られる。 -/
lemma appendIso_adjacent_right (X : C) (m n : ℕ) (i : Fin n) :
    (power X m ◁ (adjacentIso X n i).hom) ≫ (appendIso X m (n + 1)).hom =
      (appendIso X m (n + 1)).hom ≫ (adjacentIso X (m + n) (i.natAdd m)).hom := by
  induction m with
  | zero =>
    simp only [appendIso, power, Iso.trans_hom, eqToIso.hom, Category.assoc]
    rw [leftUnitor_naturality_assoc]
    erw [← adjacentIso_index_eq X (Nat.zero_add n).symm i, natAdd_zero_cast n i]
  | succ m ih =>
    simp only [appendIso, power, Iso.trans_hom, eqToIso.hom, whiskerLeftIso_hom,
      Category.assoc]
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, ih]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [← natAdd_succ_cast m n i]
    erw [adjacentIso_index_eq X (Nat.succ_add m n).symm (i.natAdd m).succ]
    simp only [adjacentIso, Fin.cases_succ, whiskerLeftIso_hom]

end SerrePositivity.TensorPowers
end

end TensorPowerBlockGenerators

/-! ## TensorPowerLeftBlock（旧 SerrePositivity/CategoryTheory/Monoidal/TensorPowerLeftBlock.lean） -/

/-!
# 左ブロックの隣接交換と反復テンソルの連結

先頭二因子の交換を尾の連結と比較し、交換位置についての帰納で左ブロック全体へ拡張する。
右ブロックの比較と同じ既存の隣接交換を用い、次数の移送を明示する。
-/

@[expose] public section TensorPowerLeftBlock
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
end

end TensorPowerLeftBlock

/-! ## TensorPowerFirstCrossing（旧 SerrePositivity/CategoryTheory/Monoidal/TensorPowerFirstCrossing.lean） -/

/-! # 反復テンソルの先頭因子を末尾へ移す

隣接交換の再帰を、braidingのhexagonと連結同型を用いた射として比較する。
このモジュールは置換作用や球面に依存しない。
-/

@[expose] public section TensorPowerFirstCrossing
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 隣接交換の再帰で先頭の因子を末尾へ送る同型。 -/
def moveFirstIso (X : C) : ∀ n, power X (n + 1) ≅ power X (n + 1)
  | 0 => Iso.refl _
  | n + 1 => swapFirstIso X n ≪≫ whiskerLeftIso X (moveFirstIso X n)
/-- 隣接交換の列は、braidingと尾への連結による射に一致する。 -/
lemma moveFirstIso_braiding (X : C) (n : ℕ) :
    (moveFirstIso X n).hom =
      (β_ X (power X n)).hom ≫ (power X n ◁ (ρ_ X).inv) ≫ (appendIso X n 1).hom := by
  induction n with
  | zero =>
    simp only [moveFirstIso, Iso.refl_hom, power, appendIso, Iso.trans_hom,
      eqToIso.hom, eqToHom_refl, Category.comp_id]
    rw [leftUnitor_naturality, braiding_leftUnitor_assoc, Iso.hom_inv_id]
  | succ n ih =>
    simp only [moveFirstIso, Iso.trans_hom, whiskerLeftIso_hom, ih]
    simp only [power, appendIso, Iso.trans_hom, whiskerLeftIso_hom,
      eqToIso.hom, eqToHom_refl, Category.comp_id]
    rw [braiding_tensor_right_hom]
    simp only [Category.assoc]
    erw [associator_naturality_right_assoc]
    simp only [Iso.inv_hom_id_assoc]
    simp only [swapFirstIso, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
      whiskerLeft_comp, Category.assoc]

/-- 第1段と尾のbraidingの後の連結は、巡回移動の前に右単位子を適用した射。 -/
@[reassoc] lemma oneCrossing_comparison (X : C) (n : ℕ) :
    (β_ (power X 1) (power X n)).hom ≫ (appendIso X n 1).hom =
      ((ρ_ X).hom ▷ power X n) ≫ (moveFirstIso X n).hom := by
  rw [moveFirstIso_braiding]
  erw [braiding_naturality_left_assoc]
  simp only [← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]
  rfl
end SerrePositivity.TensorPowers
end

end TensorPowerFirstCrossing

/-! ## TensorPowerBlockPermutations（旧 SerrePositivity/CategoryTheory/Monoidal/TensorPowerBlockPermutations.lean） -/

/-! # ブロック置換と反復テンソルの連結

左右の隣接交換の比較を、隣接互換による帰納と既存の作用の乗法則によって全置換へ拡張する。
-/

@[expose] public section TensorPowerBlockPermutations
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
end

end TensorPowerBlockPermutations

/-! ## TensorPowerFirstCrossingAction（旧 SerrePositivity/CategoryTheory/Monoidal/TensorPowerFirstCrossingAction.lean） -/

/-! # 先頭因子の移動と既存の対称群作用

有限置換の隣接互換による帰納で尾の作用を比較し、巡回置換の作用をbraidingへ接続する。
-/

@[expose] public section TensorPowerFirstCrossingAction
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open SerrePositivity.Coxeter

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 尾の置換をずらした作用は、一因子を固定した左whisker。 -/
lemma permutationAction_shift (X : C) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permutationAction X (n + 1) (shiftPerm σ)).asIso.hom =
      X ◁ (permutationAction X n σ).asIso.hom := by
  cases n with
  | zero =>
    have hs : σ = 1 := Subsingleton.elim _ _
    subst σ
    rw [shiftPerm_one, permutationAction_one, permutationAction_one, whiskerLeft_id]
    rfl
  | succ n =>
    apply permutation_induction_right σ
    · rw [shiftPerm_one, permutationAction_one, permutationAction_one, whiskerLeft_id]
      rfl
    · intro τ i ih
      simp only [shiftPerm_mul, permutationAction_mul, shiftPerm_adjacent,
        permutationAction_adjacent, ih, whiskerLeft_comp]
      rfl

/-- 先頭を末尾へ送る置換の作用は、既存の隣接交換による同型。 -/
lemma permutationAction_firstToLast (X : C) (n : ℕ) :
    (permutationAction X (n + 1) (firstToLastPerm n)).asIso.hom = (moveFirstIso X n).hom := by
  induction n with
  | zero => exact permutationAction_one X 1
  | succ n ih =>
    rw [firstToLastPerm, permutationAction_mul, permutationAction_adjacent,
      permutationAction_shift, ih]
    rfl

/-- 逆向きの巡回置換の作用は、先頭因子をbraidingで末尾へ移して連結する射。 -/
lemma permutationAction_rotate_symm (X : C) (n : ℕ) :
    (permutationAction X (n + 1) (finRotate (n + 1)).symm).asIso.hom =
      (β_ X (power X n)).hom ≫ (power X n ◁ (ρ_ X).inv) ≫ (appendIso X n 1).hom := by
  rw [← firstToLastPerm_eq_rotate_symm, permutationAction_firstToLast, moveFirstIso_braiding]

/-- 順向きの巡回置換の作用は、先頭因子を末尾へ移す同型の逆射。 -/
lemma permutationAction_rotate (X : C) (n : ℕ) :
    (permutationAction X (n + 1) (finRotate (n + 1))).asIso.hom = (moveFirstIso X n).inv := by
  have h : (permutationAction X (n + 1) (finRotate (n + 1)).symm).asIso =
      moveFirstIso X n := by
    apply Iso.ext
    rw [← Coxeter.firstToLastPerm_eq_rotate_symm, permutationAction_firstToLast]
  have hh := congrArg Iso.inv h
  simpa only [← Equiv.Perm.inv_def, map_inv, Aut.inv_asIso, Iso.symm_inv] using hh
end SerrePositivity.TensorPowers
end

end TensorPowerFirstCrossingAction
