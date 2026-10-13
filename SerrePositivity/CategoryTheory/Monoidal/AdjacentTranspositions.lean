module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPermutations

/-!
# 反復テンソルの各位置の隣接交換

n+1 個の因子に対し、n 個の隣接交換を有限添字で定義する。
先頭の交換と、先頭の因子を保った尾の交換による再帰で構成する。
-/

@[expose] public section

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
