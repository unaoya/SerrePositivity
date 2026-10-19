module

public import SerrePositivity.KST.Spectra.GroupNerveCoordinates
public import Mathlib.Data.Fin.Tuple.Basic

/-!
概要：群の nerve の面の非斉次座標での式。
方針：面が飛ばす頂点の前後で隣接辺を読み、飛ばした頂点では二つの辺を合成する。
規約：逆元を取る座標により合成は通常の順序の群の積となる。
使われ方：Goerss–Jardine VIII §2。BG の交代微分と通常の群 cochain 微分の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.GroupNerve

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (G : Type u) [Group G]

def arrowValue {n : ℕ} (s : ComposableArrows (AsSmall.{u} (SingleObj G)) n)
    (a b : Fin (n + 1)) (h : a ≤ b) : G := (s.map (homOfLE h)).down

@[congr]
lemma arrowValue_congr {n : ℕ} (s : ComposableArrows (AsSmall.{u} (SingleObj G)) n)
    {a b a' b' : Fin (n + 1)} (ha : a = a') (hb : b = b') (h : a ≤ b) (h' : a' ≤ b') :
    arrowValue G s a b h = arrowValue G s a' b' h' := by
  subst a'
  subst b'
  rfl

lemma coordinates_face {n : ℕ} (s : ComposableArrows (AsSmall.{u} (SingleObj G)) (n + 1))
    (i : Fin (n + 2)) (k : Fin n) :
    coordinates G ((nerve (AsSmall.{u} (SingleObj G))).δ i s) k =
      (arrowValue G s (i.succAbove k.castSucc) (i.succAbove k.succ)
        ((Fin.strictMono_succAbove i).monotone (Fin.castSucc_le_succ k)))⁻¹ := rfl

/-- 概要：最初の面は非斉次群座標の最初の元を落とす。
方針：零番目の頂点を飛ばす写像は Fin.succ であることを使う。
規約：n+1 単体の面を n 個の座標で表す。
使われ方：Goerss–Jardine VIII §2。群 cochain の最初の項。 -/
lemma coordinates_face_zero {n : ℕ}
    (s : ComposableArrows (AsSmall.{u} (SingleObj G)) (n + 1)) :
    coordinates G ((nerve (AsSmall.{u} (SingleObj G))).δ (0 : Fin (n + 2)) s) =
      Fin.tail (coordinates G s) := by
  funext k
  rfl

/-- 概要：残りの面は隣接座標の積を取る contraction となる。
方針：飛ばす頂点の前後で場合分けし、その頂点の両隣の射は圏の合成則で計算する。
規約：最後の面では最後の元を落とす。
使われ方：Goerss–Jardine VIII §2。非斉次群 cochain の残りの項。 -/
lemma coordinates_face_succ {n : ℕ}
    (s : ComposableArrows (AsSmall.{u} (SingleObj G)) (n + 1)) (i : Fin (n + 1)) :
    coordinates G ((nerve (AsSmall.{u} (SingleObj G))).δ i.succ s) =
      Fin.contractNth i (· * ·) (coordinates G s) := by
  funext k
  change Fin n at k
  rw [coordinates_face]
  rcases lt_trichotomy k.castSucc i with hlt | heq | hgt
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ hlt]
    have h₀ := Fin.succAbove_of_succ_le i.succ k.castSucc (by
      change k.val + 1 ≤ i.val + 1
      exact Nat.succ_le_succ (Nat.le_of_lt hlt))
    have h₁ := Fin.succAbove_of_succ_le i.succ k.succ (by
      change k.val + 1 + 1 ≤ i.val + 1
      exact Nat.succ_le_succ hlt)
    simp only [h₀, h₁]
    rfl
  · subst i
    rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl]
    have h₀ := Fin.succAbove_of_succ_le k.castSucc.succ k.castSucc le_rfl
    have h₁ := Fin.succAbove_of_le_castSucc k.castSucc.succ k.succ (by
      change k.val + 1 ≤ k.val + 1
      rfl)
    simp only [h₀, h₁]
    change ((s.map' k.val (k.val + 2) (by omega) (by omega)).down : G)⁻¹ =
      ((s.map' k.val (k.val + 1)).down : G)⁻¹ *
        ((s.map' (k.val + 1) (k.val + 2) (by omega) (by omega)).down : G)⁻¹
    rw [s.map'_comp k.val (k.val + 1) (k.val + 2) (by omega) (by omega) (by omega),
      CategoryTheory.down_comp]
    exact mul_inv_rev _ _
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ hgt]
    have h₀ := Fin.succAbove_of_le_castSucc i.succ k.castSucc (by
      change i.val + 1 ≤ k.val
      exact hgt)
    have h₁ := Fin.succAbove_of_le_castSucc i.succ k.succ (by
      change i.val + 1 ≤ k.val + 1
      exact Nat.succ_le_succ (Nat.le_of_lt hgt))
    simp only [h₀, h₁]
    rfl

end

end SerrePositivity.KST.Spectra.GroupNerve
