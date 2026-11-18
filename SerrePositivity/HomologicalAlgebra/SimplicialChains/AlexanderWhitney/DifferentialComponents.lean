module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.BoundaryExpansion
public import Mathlib.Tactic.Abel

/-!
# AW 成分と微分の可換性

概要：Berger–Fresse §1.1.4 の AW 対角についてテンソル積の微分公式を証明する。
方針：交代面和を切断点で分割し、二つの境界面が逆符号で相殺することを使う。
規約：後半の微分の符号は前半の鎖次数 p による (−1)^p。
使われ方：次数成分を束ねて AW 対角を鎖写像にする。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.Simplicial _root_.TensorProduct

private lemma last_face_segment (b : ℕ) :
    SimplexCategory.δ (Fin.last (b + 1)) = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap 0 b (b + 1) (by omega) := by
  ext k : 3
  change (Fin.last (b + 1)).succAbove k = _
  rw [Fin.succAbove_of_castSucc_lt _ _ k.castSucc_lt_last]
  apply Fin.ext
  change k.val = 0 + k.val
  omega

private lemma zero_face_segment (b : ℕ) :
    SimplexCategory.δ (0 : Fin (b + 2)) = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.segmentMap 1 b (b + 1) (by omega) := by
  ext k : 3
  change (0 : Fin (b + 2)).succAbove k = _
  rw [Fin.succAbove_of_le_castSucc _ _ (Fin.zero_le _)]
  apply Fin.ext
  change k.val + 1 = 1 + k.val
  omega

private lemma last_face_cut (X : SSet) {n : ℕ} (x : X _⦋n⦌)
    (a b : ℕ) (h : a + (b + 1) ≤ n) :
    X.δ (Fin.last (b + 1)) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x a (b + 1) h) = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x a b (by omega) := by
  change X.map (SimplexCategory.δ (Fin.last (b + 1))).op _ = _
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.last_face_segment]
  change _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x a (b + 1) h) 0 b (by omega) = _
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_cut]
  rfl

private lemma zero_face_cut (X : SSet) {n : ℕ} (x : X _⦋n⦌)
    (a b : ℕ) (h : a + (b + 1) ≤ n) :
    X.δ (0 : Fin (b + 2)) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x a (b + 1) h) = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x (a + 1) b (by omega) := by
  change X.map (SimplexCategory.δ (0 : Fin (b + 2))).op _ = _
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.zero_face_segment]
  change _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x a (b + 1) h) 1 b (by omega) = _
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_cut]

private lemma alternating_recombine {M : Type*} [AddCommGroup M] (p q : ℕ)
    (f : Fin (p + 2) → M) (g : Fin (q + 2) → M)
    (h : f (Fin.last (p + 1)) = g 0) :
    (∑ i, (-1 : ℤ) ^ i.val • f i) + (-1 : ℤ) ^ p • (∑ j, (-1 : ℤ) ^ j.val • g j) =
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ i.val • f i.castSucc) +
        ∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) • g j.succ := by
  rw [Fin.sum_univ_castSucc (fun i : Fin (p + 2) => (-1 : ℤ) ^ i.val • f i),
    Fin.sum_univ_succ (fun j : Fin (q + 2) => (-1 : ℤ) ^ j.val • g j)]
  simp only [Fin.val_last, Fin.val_castSucc, Fin.val_zero, pow_zero, one_smul,
    smul_add, Finset.smul_sum, smul_smul, Fin.val_succ]
  have hs : (-1 : ℤ) ^ (p + 1) = -((-1 : ℤ) ^ p) := by
    rw [pow_succ, mul_neg_one]
  have ht : (∑ j : Fin (q + 1), ((-1 : ℤ) ^ p * (-1 : ℤ) ^ (j.val + 1)) • g j.succ) =
      ∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) • g j.succ := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← pow_add]
    congr 2
    omega
  rw [hs, neg_smul, h, ht]
  abel

variable (A : Type u) [CommRing A]

/-- 概要：AW 成分の鎖写像の条件を正規化生成元で述べる（Berger–Fresse §1.1.4）。
方針：二つの因子の微分の交代和を展開し、共通の切断境界の二項を消す。
規約：入力の鎖次数は p+q+1、出力の二次数は p と q。
使われ方：AW 対角をテンソル鎖複体への鎖写像として構成する。 -/
lemma component_d_generator (X : SSet.{0}) (p q : ℕ) (x : X _⦋p + q + 1⦌) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X (p + q) p q rfl
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + q + 1) (p + q) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X (p + q + 1) x)) =
      ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + 1) p ▷ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X q)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X (p + q + 1) (p + 1) q (by omega)
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X (p + q + 1) x)) +
      (-1 : ℤ) ^ p • (((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X p ◁ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (q + 1) q)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X (p + q + 1) p (q + 1) (by omega)
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X (p + q + 1) x))) := by
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_generator_boundary]
  simp only [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_generator, ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_d,
    TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  symm
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.alternating_recombine
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.last_face_cut, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.zero_face_cut]

/-- 概要：正規化 AW 成分とテンソル積の微分の可換性（Berger–Fresse §1.1.4）。
方針：正規化生成元による外延性を用いて生成元公式を射の等式へ移す。
規約：p,q は任意の自然数であり、基礎環の標数を制限しない。
使われ方：全ての次数成分を束ねる際の鎖写像の条件となる。 -/
lemma component_d (X : SSet.{0}) (p q : ℕ) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + q + 1) (p + q) ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X (p + q) p q rfl =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X (p + q + 1) (p + 1) q (by omega) ≫
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + 1) p ▷ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X q) +
      (-1 : ℤ) ^ p • (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X (p + q + 1) p (q + 1) (by omega) ≫
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X p ◁ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (q + 1) q)) := by
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A X (p + q + 1)
  intro x
  change _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X (p + q) p q rfl
      ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + q + 1) (p + q) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X (p + q + 1) x)) =
    ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + 1) p ▷ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X q)
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X (p + q + 1) (p + 1) q (by omega)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X (p + q + 1) x)) +
    (-1 : ℤ) ^ p • (((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X p ◁ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (q + 1) q)
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X (p + q + 1) p (q + 1) (by omega)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X (p + q + 1) x)))
  exact _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_d_generator A X p q x

end SerrePositivity.SimplicialChains.AlexanderWhitney
