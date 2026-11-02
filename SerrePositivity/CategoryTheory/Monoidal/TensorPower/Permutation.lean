module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import SerrePositivity.GroupTheory.Coxeter.TypeA
public import SerrePositivity.GroupTheory.Coxeter.InvolutionRelations
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Monoidal.TensorPower.Permutation

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Monoidal.TensorPower.Permutation` を直接 import する。
-/

/-! ## TensorPermutations（旧 SerrePositivity/CategoryTheory/Monoidal/TensorPermutations.lean） -/

/-!
# 反復テンソルの隣接交換の基盤

最初の二因子を交換し、残りの因子をそのまま保つ同型を構成する。
対合性と対象の射に関する自然性を確認する。
全ての置換の作用を定義するには、他の位置の交換とその関係式をさらに整える必要がある。
-/

@[expose] public section TensorPermutations
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 最初の二因子を交換する反復テンソルの同型。 -/
def swapFirstIso (X : C) (n : ℕ) : power X (n + 2) ≅ power X (n + 2) :=
  (α_ X X (power X n)).symm ≪≫ whiskerRightIso (β_ X X) (power X n) ≪≫ α_ X X (power X n)

/-- 最初の二因子の交換は対合。 -/
lemma swapFirstIso_involutive (X : C) (n : ℕ) :
    (swapFirstIso X n).hom ≫ (swapFirstIso X n).hom = 𝟙 (power X (n + 2)) := by
  simp only [swapFirstIso, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry]
  simp

/-- 最初の二因子の交換は基礎圏の射と両立する。 -/
lemma swapFirstIso_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    map f (n + 2) ≫ (swapFirstIso Y n).hom =
      (swapFirstIso X n).hom ≫ map f (n + 2) := by
  simp only [swapFirstIso, map, power, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
    Category.assoc]
  rw [associator_inv_naturality_assoc]
  have h : ((f ⊗ₘ f) ⊗ₘ map f n) ≫ ((β_ Y Y).hom ▷ power Y n) =
      ((β_ X X).hom ▷ power X n) ≫ ((f ⊗ₘ f) ⊗ₘ map f n) := by
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    exact congrArg (fun k ↦ k ⊗ₘ map f n) (braiding_naturality f f)
  rw [← Category.assoc _ _ (α_ Y Y (power Y n)).hom, h, Category.assoc,
    associator_naturality]

end SerrePositivity.TensorPowers
end

end TensorPermutations

/-! ## AdjacentTranspositions（旧 SerrePositivity/CategoryTheory/Monoidal/AdjacentTranspositions.lean） -/

/-!
# 反復テンソルの各位置の隣接交換

n+1 個の因子に対し、n 個の隣接交換を有限添字で定義する。
先頭の交換と、先頭の因子を保った尾の交換による再帰で構成する。
-/

@[expose] public section AdjacentTranspositions
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- n+1 個の因子の第 i 因子と第 i+1 因子を交換する。 -/
def adjacentIso (X : C) : ∀ n, Fin n → (power X (n + 1) ≅ power X (n + 1))
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases (swapFirstIso X n)
      (fun j ↦ whiskerLeftIso X (adjacentIso X n j)) i

/-- 各位置の隣接交換は対合。 -/
lemma adjacentIso_involutive (X : C) (n : ℕ) (i : Fin n) :
    (adjacentIso X n i).hom ≫ (adjacentIso X n i).hom = 𝟙 (power X (n + 1)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact swapFirstIso_involutive X n
    · change (X ◁ (adjacentIso X n j).hom) ≫ (X ◁ (adjacentIso X n j).hom) = 𝟙 _
      rw [← whiskerLeft_comp, ih j, whiskerLeft_id]

/-- 各位置の交換は対象の射に関して自然。 -/
lemma adjacentIso_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) (i : Fin n) :
    map f (n + 1) ≫ (adjacentIso Y n i).hom =
      (adjacentIso X n i).hom ≫ map f (n + 1) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact swapFirstIso_naturality f n
    · change (f ⊗ₘ map f (n + 1)) ≫ (Y ◁ (adjacentIso Y n j).hom) =
        (X ◁ (adjacentIso X n j).hom) ≫ (f ⊗ₘ map f (n + 1))
      simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
      exact congrArg (fun k ↦ f ⊗ₘ k) (ih j)

/-- 最初の二因子の交換は、尾の任意の自己射と両立する。 -/
lemma swapFirstIso_tail_naturality (X : C) (n : ℕ) (f : power X n ⟶ power X n) :
    (X ◁ X ◁ f) ≫ (swapFirstIso X n).hom =
      (swapFirstIso X n).hom ≫ (X ◁ X ◁ f) := by
  simp only [swapFirstIso, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right]

/-- 一因子以上離れた位置の隣接交換は可換。 -/
lemma adjacentIso_commute (X : C) (n : ℕ) (i j : Fin n) (h : i.val + 1 < j.val) :
    (adjacentIso X n i).hom ≫ (adjacentIso X n j).hom =
      (adjacentIso X n j).hom ≫ (adjacentIso X n i).hom := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert h
    refine Fin.cases ?_ (fun i' ↦ ?_) i
    · refine Fin.cases ?_ (fun j' ↦ ?_) j
      · intro h
        simp at h
      · cases n with
        | zero => exact Fin.elim0 j'
        | succ m =>
          refine Fin.cases ?_ (fun k ↦ ?_) j'
          · intro h
            simp at h
          · intro h
            exact (swapFirstIso_tail_naturality X (m + 1) (adjacentIso X m k).hom).symm
    · refine Fin.cases ?_ (fun j' ↦ ?_) j
      · intro h
        simp at h
      · intro h
        change (X ◁ (adjacentIso X n i').hom) ≫ (X ◁ (adjacentIso X n j').hom) =
          (X ◁ (adjacentIso X n j').hom) ≫ (X ◁ (adjacentIso X n i').hom)
        rw [← whiskerLeft_comp, ← whiskerLeft_comp]
        exact congrArg (fun f ↦ X ◁ f) (ih i' j' (by simpa using h))

end SerrePositivity.TensorPowers
end

end AdjacentTranspositions

/-! ## AdjacentBraid（旧 SerrePositivity/CategoryTheory/Monoidal/AdjacentBraid.lean） -/

/-!
# 隣接交換の braid 関係

三因子の Yang–Baxter 恒等式を、残りの反復テンソルとの積へ延長する。
括弧付けの比較により、先頭の二つの隣接交換へ接続する。
-/

@[expose] public section AdjacentBraid
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 三因子の最初の隣接交換。 -/
def tripleFirstHom (X : C) : X ⊗ (X ⊗ X) ⟶ X ⊗ (X ⊗ X) :=
  (α_ X X X).inv ≫ (β_ X X).hom ▷ X ≫ (α_ X X X).hom

/-- 三因子の二番目の隣接交換。 -/
def tripleSecondHom (X : C) : X ⊗ (X ⊗ X) ⟶ X ⊗ (X ⊗ X) := X ◁ (β_ X X).hom

/-- 三因子を一つのブロックとしてから尾と合わせた括弧付けの比較。 -/
def tripleTailIso (X : C) (n : ℕ) :
    (X ⊗ (X ⊗ X)) ⊗ power X n ≅ power X (n + 3) :=
  (α_ X (X ⊗ X) (power X n)) ≪≫ whiskerLeftIso X (α_ X X (power X n))

@[reassoc] lemma tripleTail_first (X : C) (n : ℕ) :
    (tripleFirstHom X ▷ power X n) ≫
        (tripleTailIso X n).hom =
      (tripleTailIso X n).hom ≫ (swapFirstIso X (n + 1)).hom := by
  dsimp [tripleTailIso, swapFirstIso, tripleFirstHom, tripleSecondHom, power]
  simp only [whiskerLeftIso_hom, whiskerRightIso_hom]
  monoidal

@[reassoc] lemma tripleTail_second (X : C) (n : ℕ) :
    (tripleSecondHom X ▷ power X n) ≫ (tripleTailIso X n).hom =
      (tripleTailIso X n).hom ≫ (X ◁ (swapFirstIso X n).hom) := by
  dsimp [tripleTailIso, swapFirstIso, tripleFirstHom, tripleSecondHom, power]
  simp only [whiskerLeftIso_hom, whiskerRightIso_hom]
  monoidal

/-- 先頭の二つの隣接交換は braid 関係を満たす。 -/
lemma swapFirstIso_braid (X : C) (n : ℕ) :
    (swapFirstIso X (n + 1)).hom ≫ (X ◁ (swapFirstIso X n).hom) ≫
      (swapFirstIso X (n + 1)).hom =
    (X ◁ (swapFirstIso X n).hom) ≫ (swapFirstIso X (n + 1)).hom ≫
      (X ◁ (swapFirstIso X n).hom) := by
  apply (cancel_epi (tripleTailIso X n).hom).mp
  have hcore : tripleFirstHom X ≫ tripleSecondHom X ≫ tripleFirstHom X =
      tripleSecondHom X ≫ tripleFirstHom X ≫ tripleSecondHom X := by
    simpa only [tripleFirstHom, tripleSecondHom, Category.assoc] using yang_baxter X X X
  have h := congrArg (fun f ↦ (f ▷ power X n) ≫ (tripleTailIso X n).hom) hcore
  simp only [comp_whiskerRight, Category.assoc] at h
  rw [tripleTail_first, tripleTail_second_assoc, tripleTail_first_assoc,
    tripleTail_second, tripleTail_first_assoc, tripleTail_second_assoc] at h
  exact h

/-- 任意の隣接した二つの交換は braid 関係を満たす。 -/
lemma adjacentIso_braid (X : C) (n : ℕ) (i : Fin n) :
    (adjacentIso X (n + 1) i.castSucc).hom ≫ (adjacentIso X (n + 1) i.succ).hom ≫
      (adjacentIso X (n + 1) i.castSucc).hom =
    (adjacentIso X (n + 1) i.succ).hom ≫ (adjacentIso X (n + 1) i.castSucc).hom ≫
      (adjacentIso X (n + 1) i.succ).hom := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact swapFirstIso_braid X n
    · change (X ◁ (adjacentIso X (n + 1) j.castSucc).hom) ≫
        (X ◁ (adjacentIso X (n + 1) j.succ).hom) ≫
        (X ◁ (adjacentIso X (n + 1) j.castSucc).hom) =
      (X ◁ (adjacentIso X (n + 1) j.succ).hom) ≫
        (X ◁ (adjacentIso X (n + 1) j.castSucc).hom) ≫
        (X ◁ (adjacentIso X (n + 1) j.succ).hom)
      simpa only [whiskerLeft_comp] using congrArg (fun f ↦ X ◁ f) (ih j)

end SerrePositivity.TensorPowers
end

end AdjacentBraid

/-! ## PermutationAction（旧 SerrePositivity/CategoryTheory/Monoidal/PermutationAction.lean） -/

/-!
# 反復テンソルへの対称群作用

型 A の提示から隣接交換を自己同型群へ延長し、対称群の同型と合成する。
一般の対称モノイダル圏の結果であり、球面や smash の定義には依存しない。
-/

@[expose] public section PermutationAction
universe v u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory SerrePositivity.Coxeter

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 隣接交換を反復テンソルの自己同型群の元として読む。 -/
noncomputable def adjacentAut (X : C) (n : ℕ) (i : Fin n) :
    Aut (power X (n + 1)) := Aut.of (adjacentIso X n i)

/-- 隣接交換の自己同型は対合。 -/
lemma adjacentAut_square (X : C) (n : ℕ) (i : Fin n) :
    adjacentAut X n i * adjacentAut X n i = 1 := by
  apply Aut.ext
  apply Iso.ext
  exact adjacentIso_involutive X n i

/-- 離れた位置の隣接交換は自己同型群でも可換。 -/
lemma adjacentAut_commute (X : C) (n : ℕ) (i j : Fin n) (h : i.val + 1 < j.val) :
    adjacentAut X n i * adjacentAut X n j = adjacentAut X n j * adjacentAut X n i := by
  apply Aut.ext
  apply Iso.ext
  exact (adjacentIso_commute X n i j h).symm

/-- 隣接した二つの交換は自己同型群でも braid 関係を満たす。 -/
lemma adjacentAut_braid (X : C) (n : ℕ) (i : Fin n) :
    adjacentAut X (n + 1) i.castSucc * adjacentAut X (n + 1) i.succ *
      adjacentAut X (n + 1) i.castSucc =
    adjacentAut X (n + 1) i.succ * adjacentAut X (n + 1) i.castSucc *
      adjacentAut X (n + 1) i.succ := by
  apply Aut.ext
  apply Iso.ext
  exact adjacentIso_braid X n i

/-- 隣接交換は型 A の Coxeter 関係を満たす。 -/
lemma adjacentAut_isLiftable (X : C) (n : ℕ) :
    CoxeterMatrix.IsLiftable (CoxeterMatrix.A n) (adjacentAut X n) := by
  intro i j
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  by_cases hij : i = j
  · subst j
    simp [adjacentAut_square]
  rw [ite_eq_right hij]
  by_cases hadj : j.val + 1 = i.val ∨ i.val + 1 = j.val
  · rw [ite_eq_left hadj]
    have hstep : ∀ (a b : Fin n), a.val + 1 = b.val →
        (adjacentAut X n a * adjacentAut X n b) ^ 3 = 1 := by
      intro a b h
      cases n with
      | zero => exact Fin.elim0 a
      | succ m =>
        have hlast : a ≠ Fin.last m := by
          intro hh
          subst a
          simp only [Fin.val_last] at h
          omega
        let k := a.castPred hlast
        have hk : k.castSucc = a := Fin.castSucc_castPred a hlast
        have hb : k.succ = b := by apply Fin.ext; simpa [k] using h
        have hbraid := adjacentAut_braid X m k
        rw [hk, hb] at hbraid
        exact involution_pair_cube _ _ (adjacentAut_square X _ a)
          (adjacentAut_square X _ b) hbraid
    rcases hadj with hji | hij'
    · have hrev := hstep j i hji
      have hi : (adjacentAut X n i)⁻¹ = adjacentAut X n i :=
        inv_eq_of_mul_eq_one_right (adjacentAut_square X n i)
      have hj : (adjacentAut X n j)⁻¹ = adjacentAut X n j :=
        inv_eq_of_mul_eq_one_right (adjacentAut_square X n j)
      have hc := congrArg (fun g ↦ g⁻¹) hrev
      simpa only [← inv_pow, mul_inv_rev, inv_one, hi, hj] using hc
    · exact hstep i j hij'
  · rw [ite_eq_right hadj]
    have hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val := by omega
    have hc : adjacentAut X n i * adjacentAut X n j =
        adjacentAut X n j * adjacentAut X n i := by
      rcases hfar with h | h
      · exact adjacentAut_commute X n i j h
      · exact (adjacentAut_commute X n j i h).symm
    exact involution_pair_square _ _ (adjacentAut_square X n i) (adjacentAut_square X n j) hc

/-- 正次数の反復テンソルに対する対称群の作用。 -/
noncomputable def positivePermutationAction (X : C) (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) →* Aut (power X (n + 1)) :=
  ((CoxeterMatrix.A n).toCoxeterSystem.lift ⟨adjacentAut X n, adjacentAut_isLiftable X n⟩).comp
    (typeAEquivPerm n).symm.toMonoidHom

/-- 標準の隣接互換は構成済みの隣接交換へ送られる。 -/
lemma positivePermutationAction_adjacent (X : C) (n : ℕ) (i : Fin n) :
    positivePermutationAction X n (adjacentTransposition i) = adjacentAut X n i := by
  have hi : (typeAEquivPerm n).symm (adjacentTransposition i) =
      (CoxeterMatrix.A n).simple i := by
    rw [← typeAEquivPerm_simple n i]
    exact (typeAEquivPerm n).symm_apply_apply _
  change ((CoxeterMatrix.A n).toCoxeterSystem.lift
    ⟨adjacentAut X n, adjacentAut_isLiftable X n⟩)
      ((typeAEquivPerm n).symm (adjacentTransposition i)) = adjacentAut X n i
  rw [hi]
  exact CoxeterSystem.lift_apply_simple _ _ _

/-- 第0段も含む全次数の置換作用。第0段の置換は単位へ送る。 -/
noncomputable def permutationAction (X : C) :
    ∀ n, Equiv.Perm (Fin n) →* Aut (power X n)
  | 0 => 1
  | n + 1 => positivePermutationAction X n

/-- 全次数の作用における隣接互換の値。 -/
lemma permutationAction_adjacent (X : C) (n : ℕ) (i : Fin n) :
    permutationAction X (n + 1) (adjacentTransposition i) = adjacentAut X n i :=
  positivePermutationAction_adjacent X n i

/-- 恒等置換は恒等射へ送られる。 -/
lemma permutationAction_one (X : C) (n : ℕ) :
    (permutationAction X n 1).asIso.hom = 𝟙 (power X n) :=
  congrArg (fun a : Aut (power X n) ↦ a.asIso.hom) ((permutationAction X n).map_one)

/-- 置換の乗法は圏の合成と逆の順序で両立する。 -/
lemma permutationAction_mul (X : C) (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    (permutationAction X n (σ * τ)).asIso.hom =
      (permutationAction X n τ).asIso.hom ≫ (permutationAction X n σ).asIso.hom :=
  congrArg (fun a : Aut (power X n) ↦ a.asIso.hom) ((permutationAction X n).map_mul σ τ)

/-- 第0段では全ての置換が恒等射へ送られる。 -/
lemma permutationAction_zero (X : C) (σ : Equiv.Perm (Fin 0)) :
    (permutationAction X 0 σ).asIso.hom = 𝟙 (power X 0) := rfl

end SerrePositivity.TensorPowers

end PermutationAction
