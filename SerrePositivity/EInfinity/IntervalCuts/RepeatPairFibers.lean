module

public import SerrePositivity.EInfinity.IntervalCuts.RegularFactorValues

/-!
# 反復位置対と非零切断・区切り位置の有限同値

概要：Berger–Fresse §2.2.7 の全反復色を非零元切断と区切りの依存組で数える。
方針：後の同色出現は非零切断の右側の単射性で一意に定まる。
規約：区切り位置自身は切断点より前。
使われ方：反復色因子境界和を元の活動位置の境界和へ接続する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection
open scoped BigOperators

variable {n l : ℕ} {u : Fin l → Fin n}

/-- 概要：反復位置対を非零切断と前出現の区切りへ送る（BF §2.2.7）。
方針：後出現を区切りの証人として使う。
規約：後の位置を像へ追加しない。
使われ方：全反復色境界和の有限添字替え。 -/
def repeatPairFiberMap (c : RepeatCutPair u) :
    Σ _ : {p : Fin l // EdgeNondegenerate u p}, {a : Fin l // Caesura u a} :=
  ⟨⟨c.pivot, c.nondegenerate⟩, ⟨c.left, c.right, c.ordered, c.same_color.symm⟩⟩

/-- 概要：非零切断と区切りは反復位置対を一意に定める（BF §2.2.7）。
方針：前出現と元切断点を固定し、後出現を右側単射性で比較する。
規約：後出現も切断点より後にある。
使われ方：有限同値の単射側。 -/
lemma repeatPairFiberMap_injective : Function.Injective (repeatPairFiberMap (u := u)) := by
  intro c e he
  have hp := congrArg (fun z => z.1.val) he
  have ha := congrArg (fun z => z.2.val) he
  change c.pivot = e.pivot at hp
  change c.left = e.left at ha
  apply RepeatCutPair.ext hp ha
  exact edge_right_injective c.nondegenerate c.right e.right c.straddles.2.le
    (by rw [hp]; exact e.straddles.2.le)
    ((c.same_color.symm.trans (congrArg u ha)).trans e.same_color)

/-- 概要：全ての非零切断と区切りから反復位置対を構成できる（BF §2.2.7）。
方針：区切りの後同色出現を取る。
規約：証人の選択は位置対の一意性により重複を作らない。
使われ方：有限同値の全射側。 -/
lemma repeatPairFiberMap_surjective : Function.Surjective (repeatPairFiberMap (u := u)) := by
  rintro ⟨⟨p, hp⟩, ⟨a, ha⟩⟩
  obtain ⟨b, hab, hu⟩ := ha
  exact ⟨⟨p, a, b, hp, hab, hu.symm⟩, rfl⟩

/-- 概要：反復位置対と非零切断・区切りの依存組の有限同値（BF §2.2.7）。
方針：後出現を忘れる写像の全単射性を使う。
規約：元切断点と区切りを保つ。
使われ方：反復色全因子境界を元切断ごとに足す。 -/
def repeatPairFiberEquiv : RepeatCutPair u ≃
    (Σ _ : {p : Fin l // EdgeNondegenerate u p}, {a : Fin l // Caesura u a}) :=
  Equiv.ofBijective repeatPairFiberMap ⟨repeatPairFiberMap_injective, repeatPairFiberMap_surjective⟩

/-- 概要：全反復位置対の因子境界和は非零切断ごとの全区切り因子境界和（BF §2.2.7）。
方針：有限同値と依存組の和公式を使う。
規約：実際の共通次数の因子境界値を保持する。
使われ方：正規化全削除和と全活動位置境界の最終比較。 -/
lemma sum_repeatPair_factorBoundary (A : Type u) [CommRing A] {n d : ℕ}
    (u : BasisWord n d) :
    (∑ c : RepeatCutPair u.val, factorBoundaryValue A u c.pivot c.nondegenerate (u.val c.left)) =
      ∑ p : {p : Fin (n + d) // EdgeNondegenerate u.val p},
        ∑ a : {a : Fin (n + d) // Caesura u.val a},
          factorBoundaryValue A u p.val p.property (u.val a.val) := by
  classical
  calc
    _ = ∑ z : Σ p : {p : Fin (n + d) // EdgeNondegenerate u.val p},
        {a : Fin (n + d) // Caesura u.val a},
          factorBoundaryValue A u z.1.val z.1.property (u.val z.2.val) :=
      Fintype.sum_equiv repeatPairFiberEquiv _ _ (fun _ => rfl)
    _ = _ := by rw [Fintype.sum_sigma]

end SerrePositivity.EInfinity.IntervalCuts
