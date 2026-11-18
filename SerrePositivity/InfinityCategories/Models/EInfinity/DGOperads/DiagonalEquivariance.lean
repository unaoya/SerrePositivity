module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorNaturality

/-!
模型。文献の定義との比較は後で
# 隣接交換による全置換の等変性の判定

概要：Berger–Moerdijk §1 の代数の対称群関係を隣接交換だけで判定する。
方針：隣接互換が対称群をモノイドとして生成することと、対角作用の合成則を使う。
規約：対称列とテンソル冪の置換作用を同じ向きで用いる。
使われ方：Schur 作用の隣接交換の等式から任意の置換に関する代数公理を得る。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers _root_.SerrePositivity.Coxeter

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- 概要：隣接交換の対角作用を消す射は全ての置換の対角作用を消す（Berger–Moerdijk §1）。
方針：隣接互換のモノイド閉包で帰納し、恒等射と合成について不変性を示す。
規約：外側の係数の arity は n+1、終域は任意の複体。
使われ方：自由代数の作用の外側等変性を隣接交換の検証へ帰着する。 -/
lemma tensorDiagonal_equivariance_of_adjacent (P : _root_.SerrePositivity.SymmetricSequence (Complex A))
    (X Y : Complex A) (n : ℕ)
    (f : _root_.SerrePositivity.SymmetricSequence.level P (n + 1) ⊗ power X (n + 1) ⟶ Y)
    (h : ∀ i : Fin n,
      (P.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 1) (adjacentTransposition i)) ⊗ₘ
        (adjacentIso X n i).hom) ≫ f = f)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (P.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 1) σ) ⊗ₘ
      (permutationAction X (n + 1) σ).asIso.hom) ≫ f = f := by
  have hs : σ ∈ Submonoid.closure
      (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top _
  induction hs using Submonoid.closure_induction with
  | mem σ hs =>
    obtain ⟨i, rfl⟩ := hs
    change (P.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 1) (adjacentTransposition i)) ⊗ₘ
      (permutationAction X (n + 1) (adjacentTransposition i)).asIso.hom) ≫ f = f
    rw [permutationAction_adjacent]
    exact h i
  | one =>
    simp only [_root_.SerrePositivity.FiniteBijection.permutation_one, P.map_id, permutationAction_one,
      tensorHom_id, id_whiskerRight, Category.id_comp]
  | mul σ τ _ _ hσ hτ =>
    rw [_root_.SerrePositivity.FiniteBijection.permutation_mul, P.map_comp, permutationAction_mul,
      ← tensorHom_comp_tensorHom, Category.assoc, hσ, hτ]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
