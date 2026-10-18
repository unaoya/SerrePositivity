module

public import SerrePositivity.KST.Spectra.LinearGroupCochains
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
概要：線形な非斉次 cochain の余面と交代余面微分の具体式。
方針：離散係数の単体集合の余面の計算を線形係数へ移し、余面の交代和を展開する。
規約：交代符号は整数倍として記述する。
使われ方：Goerss–Jardine VIII §2。Mathlib の非斉次群 cochain 微分への実際の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.LinearGroupCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k G : Type u} [CommRing k] [Group G]

lemma coface_zero (A : Action (ModuleCat.{u} k) G) (n : ℕ)
    (x : (Fin n → G) → A.V) (s : Fin (n + 1) → G) :
    ((obj A).map (SimplexCategory.δ (0 : Fin (n + 2)))).hom x s =
      (A.ρ (s 0)).asHom.hom (x (Fin.tail s)) :=
  GroupActionCochains.functionCochains_δ_zero (discreteAction A) n (Opposite.op ⦋0⦌) x s

lemma coface_succ (A : Action (ModuleCat.{u} k) G) (n : ℕ) (j : Fin (n + 1))
    (x : (Fin n → G) → A.V) (s : Fin (n + 1) → G) :
    ((obj A).map (SimplexCategory.δ j.succ)).hom x s = x (Fin.contractNth j (· * ·) s) :=
  GroupActionCochains.functionCochains_δ_succ (discreteAction A) n j (Opposite.op ⦋0⦌) x s

/-- 概要：線形な非斉次 cochain の交代余面微分は標準の群 cochain の式になる。
方針：零番目の余面と残る余面を分け、座標ごとに交代和を計算する。
規約：符号は (-1:ℤ) の冪による整数倍。
使われ方：Goerss–Jardine VIII §2。標準の非斉次群 cochain 複体との同定。 -/
lemma alternating_d_apply (A : Action (ModuleCat.{u} k) G) (n : ℕ)
    (x : (Fin n → G) → A.V) (s : Fin (n + 1) → G) :
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (obj A) n).hom x s =
      (A.ρ (s 0)).asHom.hom (x (Fin.tail s)) +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • x (Fin.contractNth j (· * ·) s) := by
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    ModuleCat.hom_add, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, CosimplicialObject.δ]
  let z : (Fin (n + 1) → G) → A.V :=
    ((obj A).map (SimplexCategory.δ (0 : Fin (n + 2)))).hom x
  let y : Fin (n + 1) → ((Fin (n + 1) → G) → A.V) :=
    fun j ↦ ((obj A).map (SimplexCategory.δ j.succ)).hom x
  change (z + ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • y j) s = _
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  dsimp only [z, y]
  simp only [coface_zero, coface_succ]

end

end SerrePositivity.KST.Spectra.LinearGroupCochains
