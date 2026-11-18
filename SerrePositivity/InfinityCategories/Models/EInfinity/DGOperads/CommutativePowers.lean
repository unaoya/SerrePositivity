module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.MonoidPowers
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Permutation

/-!
模型。文献の定義との比較は後で
# 可換モノイド対象の反復積の置換不変性

概要：BM §1 の Com 代数の対称群等変性を反復積から得る。
方針：隣接交換で積が変わらないことを示し、対称群の生成性を用いる。
規約：空積を含む全 arity、既存の置換作用。
使われ方：離散可換代数の Com 代数構造。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open _root_.SerrePositivity.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  (X : C) [MonObj X] [IsCommMonObj X]

attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

/-- 概要：隣接する二入力の交換で反復積は変わらない（BM §1）。
方針：最初の二入力は可換性、後の位置は右括弧の再帰を使う。
規約：交換可能な位置がない場合も含む。
使われ方：全置換での対称群等変性。 -/
lemma powerProduct_adjacent (n : ℕ) (i : Fin n) :
    (adjacentIso X n i).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X (n + 1) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X (n + 1) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [adjacentIso, Fin.cases_zero, swapFirstIso, Iso.trans_hom, Iso.symm_hom,
        whiskerRightIso_hom, Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct]
      simp only [mon_tauto]
    · change (X ◁ (adjacentIso X n j).hom) ≫
        (X ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X (n + 1)) ≫ μ[X] = _
      rw [← whiskerLeft_comp_assoc, ih]
      rfl

/-- 概要：全入力置換で可換モノイド対象の反復積は変わらない（BM §1）。
方針：隣接交換による対称群の生成を使う。
規約：arity 零も含む。
使われ方：Com の代数作用の等変性公理。 -/
lemma powerProduct_permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permutationAction X n σ).asIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X n = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct X n := by
  cases n with
  | zero => rw [permutationAction_zero, Category.id_comp]
  | succ n =>
    have hs : σ ∈ Submonoid.closure
        (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top _
    induction hs using Submonoid.closure_induction with
    | mem σ hs =>
      obtain ⟨i, rfl⟩ := hs
      change (permutationAction X (n + 1) (_root_.SerrePositivity.Coxeter.adjacentTransposition i)).asIso.hom ≫ _ = _
      rw [permutationAction_adjacent]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct_adjacent X n i
    | one => rw [permutationAction_one, Category.id_comp]
    | mul σ τ _ _ hσ hτ => rw [permutationAction_mul, Category.assoc, hσ, hτ]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
