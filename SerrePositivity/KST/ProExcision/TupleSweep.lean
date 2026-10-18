module
public import SerrePositivity.KST.ProExcision.TupleAction

/-!
# prefix 作用を有限合成として構成する

概要：g₀,…,gᵣ₋₁ の順に指定座標の作用を適用する。
方針：最初の k 段を再帰的に合成し、各座標で prefix の積を計算する。
規約：KST Proposition A.1 の逆順の語の座標。
使われ方：各行の比較の局所化同値性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite MonoidalCategory
open SerrePositivity.KST.Comparison SerrePositivity.SimplicialModel
variable {G H : SimplicialObject MonCat.{u}}

/-- 概要：最初の k 個の語の元の逆順積。
方針：後の元を左に掛ける再帰。
規約：KST Proposition A.1 の nerve の語。使われ方：各行の比較の座標式。 -/
def tuplePrefixProduct {M : Type*} [Monoid M] {r : ℕ} (g : Fin r → M) :
    (k : ℕ) → k ≤ r → M
  | 0, _ => 1
  | k + 1, hk => g ⟨k, by omega⟩ * tuplePrefixProduct g k (by omega)

/-- 概要：指定座標の作用の最初の k 段の合成。
方針：第 k 段をそれまでの合成の後に置く。
規約：KST Proposition A.1。使われ方：各行の prefix 比較の分解。 -/
def tupleActionSweep (A : SimplicialMonoidAction G H) {r : ℕ} : (k : ℕ) → k ≤ r →
    (monoidTupleSpace G r ⊗ monoidSpace (tupleMonoid H r) ⟶
      monoidTupleSpace G r ⊗ monoidSpace (tupleMonoid H r))
  | 0, _ => 𝟙 _
  | k + 1, hk => tupleActionSweep A k (by omega) ≫ tupleActionStep A ⟨k, by omega⟩

/-- 概要：prefix 作用の各有限合成は局所化で可逆。
方針：各段の作用の族の可逆性と有限合成の保存を使う。
規約：KST Proposition A.1、G の群状性のみ。
使われ方：行の比較を同値と判定する代数的部分。 -/
theorem tupleActionSweep_localized_isIso (A : SimplicialMonoidAction G H)
    (hG : SimplicialMonoid.IsGrouplike G) {r : ℕ} (k : ℕ) (hk : k ≤ r) :
    IsIso (AnodyneHomotopy.anodyneQ.map (tupleActionSweep A k hk)) := by
  induction k with
  | zero =>
    change IsIso (AnodyneHomotopy.anodyneQ.map (𝟙 _))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  | succ k ih =>
    change IsIso (AnodyneHomotopy.anodyneQ.map
      (tupleActionSweep A k (by omega) ≫ tupleActionStep A ⟨k, by omega⟩))
    rw [CategoryTheory.Functor.map_comp]
    haveI := ih (by omega)
    haveI := tupleActionStep_localized_isIso A hG (⟨k, by omega⟩ : Fin r)
    infer_instance

/-- 概要：prefix 作用の合成は G のパラメータを変えない。
方針：各段の作用の族の第一成分は恒等。
規約：KST Proposition A.1。使われ方：次の段で用いる作用元の計算。 -/
lemma tupleActionSweep_base (A : SimplicialMonoidAction G H) {r : ℕ}
    (k : ℕ) (hk : k ≤ r) (n : SimplexCategoryᵒᵖ)
    (g : Fin r → G.obj n) (h : Fin r → H.obj n) :
    ((tupleActionSweep A k hk).app n (g, h)).1 = g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((tupleActionSweep A k (by omega)).app n (g, h)).1 = g
    exact ih (by omega)

/-- 概要：最初の k 段の合成の第 j 成分は該当する prefix の作用。
方針：j≥k かどうかで次の段が作用するかを分ける。
規約：KST Proposition A.1。使われ方：transport 比較と有限合成の同定。 -/
lemma tupleActionSweep_fiber (A : SimplicialMonoidAction G H) {r : ℕ}
    (k : ℕ) (hk : k ≤ r) (n : SimplexCategoryᵒᵖ)
    (g : Fin r → G.obj n) (h : Fin r → H.obj n) (j : Fin r) :
    ((tupleActionSweep A k hk).app n (g, h)).2 j =
      A.action n (tuplePrefixProduct g (min k (j.val + 1)) (by omega)) (h j) := by
  induction k with
  | zero =>
    change h j = A.action n 1 (h j)
    rw [map_one]
    rfl
  | succ k ih =>
    change (if (⟨k, by omega⟩ : Fin r) ≤ j then
        A.action n (((tupleActionSweep A k (by omega)).app n (g, h)).1 ⟨k, by omega⟩)
          (((tupleActionSweep A k (by omega)).app n (g, h)).2 j)
      else ((tupleActionSweep A k (by omega)).app n (g, h)).2 j) = _
    rw [tupleActionSweep_base, ih (by omega)]
    by_cases hj : k ≤ j.val
    · have hb : min k (j.val + 1) = k := min_eq_left (by omega)
      have ha : min (k + 1) (j.val + 1) = k + 1 := min_eq_left (by omega)
      simp only [show (⟨k, by omega⟩ : Fin r) ≤ j from hj, ite_true, hb, ha,
        tuplePrefixProduct]
      rw [map_mul]
      rfl
    · have hb : min k (j.val + 1) = j.val + 1 := min_eq_right (by omega)
      have ha : min (k + 1) (j.val + 1) = j.val + 1 := min_eq_right (by omega)
      simp only [show ¬ (⟨k, by omega⟩ : Fin r) ≤ j from hj, ite_false, hb, ha]

end SerrePositivity.KST.ProExcision
