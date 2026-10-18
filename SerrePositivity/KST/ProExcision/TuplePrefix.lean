module
public import SerrePositivity.KST.ProExcision.TupleSweep

/-!
# nerve の合成射と prefix の積

概要：始点から k 番目までの射のラベルを、逆順の prefix の積として計算する。
方針：射列の合成則で帰納する。
規約：KST Proposition A.1 の逆順の語の座標。
使われ方：transport 比較と有限個の作用の合成の同定。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
open SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 概要：nerve の始点からの射のラベルは prefix の逆順積。
方針：0→k→k+1 の射の合成を使い、隣接ラベルを左から掛ける。
規約：KST Proposition A.1。使われ方：比較の H 成分の座標計算。 -/
lemma monoidNerve_prefix_eq (M : MonCat.{u}) {r : ℕ}
    (p : (nerve (SingleObj M)) _⦋r⦌) (k : ℕ) (hk : k ≤ r) :
    (show M from p.map' 0 k (by omega) hk) =
      tuplePrefixProduct (monoidWordLabels M p) k hk := by
  induction k with
  | zero =>
    change (show M from p.map' 0 0) = 1
    rw [p.map'_self 0 (Nat.zero_le r)]
    rfl
  | succ k ih =>
    rw [p.map'_comp 0 k (k + 1) (by omega) (by omega) hk, SingleObj.comp_as_mul]
    change monoidWordLabels M p ⟨k, by omega⟩ *
      (show M from p.map' 0 k (Nat.zero_le k) (Nat.le_of_succ_le hk)) =
      monoidWordLabels M p ⟨k, by omega⟩ *
        tuplePrefixProduct (monoidWordLabels M p) k (by omega)
    rw [ih (by omega)]

end SerrePositivity.KST.ProExcision
