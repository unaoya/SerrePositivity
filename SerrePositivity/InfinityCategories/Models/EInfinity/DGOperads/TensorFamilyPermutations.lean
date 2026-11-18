module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowers
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Blocks

/-!
模型。文献の定義との比較は後で
# 入力ブロック内の置換と有限テンソルの連結

概要：Berger–Moerdijk §1 の Schur 合成で必要な、内側の入力の置換の連結を構成する。
方針：各ブロック内の置換を再帰的に連結し、テンソル冪の二つのブロックの等変性を適用する。
規約：空のブロック族と arity 0 のブロックを含む。符号は Koszul 対称性に含まれる。
使われ方：自由代数の演算を各入力の coinvariant 関係に沿って降ろす。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

/-- 概要：各入力ブロック内の置換を全入力の置換へ連結する（Berger–Moerdijk §1）。
方針：先頭ブロックと残りのブロックの置換を `blockEquiv` でまとめる。
規約：ブロックの順序は変えず、ブロックの長さの総和の等式で移送する。
使われ方：全入力へのオペラッド合成の内側等変性に現れる出力置換となる。 -/
def tensorFamilyPermutation : ∀ (n : ℕ) (s : Fin n → ℕ),
    (∀ i, Equiv.Perm (Fin (s i))) → Equiv.Perm (Fin (∑ i, s i))
  | 0, _, _ => 1
  | n + 1, s, τ =>
    (finCongr (Fin.sum_univ_succ s).symm).permCongr
      (_root_.SerrePositivity.FiniteBijection.blockEquiv (τ 0)
        (tensorFamilyPermutation n (fun i => s i.succ) (fun i => τ i.succ)))

variable {A : Type u} [CommRing A]

/-- 概要：テンソル冪の有限族の連結は各ブロック内の置換と両立する（Berger–Moerdijk §1）。
方針：族の長さで帰納し、二つのブロックの連結の等変性と次数移送の自然性を使う。
規約：各因子の置換は Koszul 符号付きの既存の作用である。
使われ方：自由代数の生成射の内側等変性で入力側の置換を連結後へ移す。 -/
lemma tensorPowerFamilyIso_permutation (K : Complex A) (n : ℕ) (s : Fin n → ℕ)
    (τ : ∀ i, Equiv.Perm (Fin (s i))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => (permutationAction K (s i) (τ i)).asIso.hom) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n s).hom =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n s).hom ≫
          (permutationAction K (∑ i, s i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation n s τ)).asIso.hom := by
  induction n with
  | zero =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation, permutationAction_one,
      Category.id_comp, Category.comp_id]
  | succ n ih =>
    have ht :
        ((permutationAction K (s 0) (τ 0)).asIso.hom ⊗ₘ
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => (permutationAction K (s i.succ) (τ i.succ)).asIso.hom)) ≫
            (power K (s 0) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun i => s i.succ)).hom) =
        (power K (s 0) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun i => s i.succ)).hom) ≫
          ((permutationAction K (s 0) (τ 0)).asIso.hom ⊗ₘ
            (permutationAction K (∑ i : Fin n, s i.succ)
              (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation n (fun i => s i.succ) (fun i => τ i.succ))).asIso.hom) := by
      simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
      rw [ih]
    change ((permutationAction K (s 0) (τ 0)).asIso.hom ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => (permutationAction K (s i.succ) (τ i.succ)).asIso.hom)) ≫ _ = _
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso, Iso.trans_hom, whiskerLeftIso_hom, eqToIso.hom,
      Category.assoc]
    rw [← Category.assoc _ _ ((appendIso K (s 0) (∑ i : Fin n, s i.succ)).hom ≫ _), ht]
    simp only [Category.assoc]
    rw [← Category.assoc _ (appendIso K (s 0) (∑ i : Fin n, s i.succ)).hom,
      appendIso_block_permutation]
    simp only [Category.assoc]
    exact congrArg ((power K (s 0) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun i => s i.succ)).hom) ≫
      (appendIso K (s 0) (∑ i : Fin n, s i.succ)).hom ≫ ·)
      (permutationAction_index_eq K (Fin.sum_univ_succ s).symm
        (_root_.SerrePositivity.FiniteBijection.blockEquiv (τ 0)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation n (fun i => s i.succ) (fun i => τ i.succ)))).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
