module
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Data.Finset.Card
/-!
概要：κ個以下の行に有限個ずつ現れる係数の総数をκで抑える。
方針：有限 support の直和の基数を、行数とκの積で評価する。
規約：列全体の基数と係数環の基数は仮定しない。
使われ方：c′ の自由直和間閉射の係数をκ提示へ取り込む。
-/
@[expose] public section
universe u
namespace SerrePositivity.DifferentialGraded

lemma finiteRowCoefficientIndex_cardinal_le {I J : Type u} (support : I → Finset J)
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ) :
    Cardinal.mk (Σ i, (support i : Set J)) ≤ κ := by
  classical
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun i => Cardinal.mk (support i : Set J)) ≤
        Cardinal.sum (fun _ : I => κ) :=
      Cardinal.sum_le_sum _ _ (fun i => (Cardinal.lt_aleph0_of_finite (support i : Set J)).le.trans hκ)
    _ = Cardinal.mk I * κ := Cardinal.sum_const' I κ
    _ ≤ κ := Cardinal.mul_le_of_le hκ hI le_rfl

end SerrePositivity.DifferentialGraded
