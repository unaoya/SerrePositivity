module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalCutComparison
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionHorizontalFaithful

/-!
概要：全単体のplusの切れ目とminusの共有点を追跡し、全次数でそれらを比較する。
方針：plusの切れ目は逆向きの区間表示、minusの共有点は元の単調射で移す。
規約：実単体の各頂点と全ての射の可換条件を保持する。
使われ方：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子的な分解の一意性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：全単体のplusの切れ目の追跡データ。
方針：全頂点の切れ目を、実区間表示の逆向きの可換条件で結ぶ。
規約：外側の切れ目を含み、因子の端点条件は別に照合する。
使われ方：Riehl–Verity Proposition 3.1.10 の水平分解の切れ目。 -/
structure WalkingAdjunctionPlusCut {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) where
  value (i : Fin (n + 1)) : Fin (walkingAdjunctionOrdinalCard X Y (F.obj i) + 1)
  naturality {i j : Fin (n + 1)} (h : i ≤ j) :
    ordinalIntervalMap (walkingAdjunctionOrderHom (F.map (homOfLE h))) (value j) = value i

/-- 概要：全単体のminusの共有点の追跡データ。
方針：全頂点の実点を、元の有限単調射の可換条件で結ぶ。
規約：空の頂点があればこのデータは存在しない。
使われ方：Riehl–Verity Proposition 3.1.10 の水平分解の共有点。 -/
structure WalkingAdjunctionMinusCut {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) where
  value (i : Fin (n + 1)) : Fin (walkingAdjunctionOrdinalCard X Y (F.obj i))
  naturality {i j : Fin (n + 1)} (h : i ≤ j) :
    walkingAdjunctionOrderHom (F.map (homOfLE h)) (value i) = value j

variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：plusの切れ目は全頂点の値で区別できる。
方針：値の関数の外延性と証明非依存性を使う。
規約：全射の条件を捨てていない。使われ方：Riehl–Verity Proposition 3.1.10。 -/
@[ext] lemma WalkingAdjunctionPlusCut.ext {a b : WalkingAdjunctionPlusCut F}
    (h : ∀ i, a.value i = b.value i) : a = b := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  have hab : a = b := funext h
  subst b
  rfl

/-- 概要：minusの共有点も全頂点の値で区別できる。
方針：値の関数の外延性と証明非依存性を使う。
規約：同じ全単体。使われ方：Riehl–Verity Proposition 3.1.10。 -/
@[ext] lemma WalkingAdjunctionMinusCut.ext {a b : WalkingAdjunctionMinusCut F}
    (h : ∀ i, a.value i = b.value i) : a = b := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  have hab : a = b := funext h
  subst b
  rfl

/-- 概要：終頂点でのplusの切れ目の順序は全頂点へ戻る。
方針：実区間表示の単調性と全射の可換条件を使う。
規約：始点を含む。使われ方：Riehl–Verity Proposition 3.1.10 の切れ目の比較。 -/
lemma WalkingAdjunctionPlusCut.le (a b : WalkingAdjunctionPlusCut F)
    (h : a.value (Fin.last n) ≤ b.value (Fin.last n)) (i : Fin (n + 1)) :
    a.value i ≤ b.value i := by
  rw [← a.naturality (Fin.le_last i), ← b.naturality (Fin.le_last i)]
  exact (ordinalIntervalMap _).monotone h

/-- 概要：plusの切れ目は終頂点の値から一意に決まる。
方針：両方向の順序を全頂点へ戻す。規約：全次数を含む。
使われ方：Riehl–Verity Proposition 3.1.10 の水平分解の比較。 -/
lemma WalkingAdjunctionPlusCut.last_injective :
    Function.Injective (fun a : WalkingAdjunctionPlusCut F => a.value (Fin.last n)) := by
  intro a b h
  exact WalkingAdjunctionPlusCut.ext (fun i => le_antisymm (a.le b h.le i) (b.le a h.ge i))

/-- 概要：二つのplusの切れ目は全頂点で同じ向きに比較できる。
方針：終頂点の全順序を戻す。規約：頂点ごとに比較の向きを変えない。
使われ方：Riehl–Verity Proposition 3.1.10 の原子的な分解の一意性。 -/
lemma WalkingAdjunctionPlusCut.total (a b : WalkingAdjunctionPlusCut F) :
    (∀ i, a.value i ≤ b.value i) ∨ (∀ i, b.value i ≤ a.value i) := by
  rcases le_total (a.value (Fin.last n)) (b.value (Fin.last n)) with h | h
  · exact Or.inl (a.le b h)
  · exact Or.inr (b.le a h)

/-- 概要：始頂点でのminusの共有点の順序は全頂点へ進む。
方針：元の有限単調射の単調性と可換条件を使う。
規約：終頂点を含む。使われ方：Riehl–Verity Proposition 3.1.10 の共有点の比較。 -/
lemma WalkingAdjunctionMinusCut.le (a b : WalkingAdjunctionMinusCut F)
    (h : a.value 0 ≤ b.value 0) (i : Fin (n + 1)) : a.value i ≤ b.value i := by
  rw [← a.naturality (Fin.zero_le i), ← b.naturality (Fin.zero_le i)]
  exact (walkingAdjunctionOrderHom _).monotone h

/-- 概要：minusの共有点は始頂点の値から一意に決まる。
方針：両方向の順序を全頂点へ進める。規約：全次数を含む。
使われ方：Riehl–Verity Proposition 3.1.10 の水平分解の比較。 -/
lemma WalkingAdjunctionMinusCut.first_injective :
    Function.Injective (fun a : WalkingAdjunctionMinusCut F => a.value 0) := by
  intro a b h
  exact WalkingAdjunctionMinusCut.ext (fun i => le_antisymm (a.le b h.le i) (b.le a h.ge i))

/-- 概要：二つのminusの共有点は全頂点で同じ向きに比較できる。
方針：始頂点の全順序を進める。規約：全射の可換条件を使う。
使われ方：Riehl–Verity Proposition 3.1.10 の原子的な分解の一意性。 -/
lemma WalkingAdjunctionMinusCut.total (a b : WalkingAdjunctionMinusCut F) :
    (∀ i, a.value i ≤ b.value i) ∨ (∀ i, b.value i ≤ a.value i) := by
  rcases le_total (a.value 0) (b.value 0) with h | h
  · exact Or.inl (a.le b h)
  · exact Or.inr (b.le a h)

/-- 概要：共有点がplusの切れ目より左にあるという条件は全頂点で不変。
方針：Galois対応の切れ目の判定と、二種類の可換条件を合わせる。
規約：異なる型の座標は自然数の値で比較する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionCut_mixed_iff (a : WalkingAdjunctionPlusCut F)
    (b : WalkingAdjunctionMinusCut F) (i : Fin (n + 1)) :
    (b.value i).val < (a.value i).val ↔ (b.value 0).val < (a.value 0).val := by
  have h := ordinalIntervalMap_cut_iff
    (walkingAdjunctionOrderHom (F.map (homOfLE (Fin.zero_le i)))) (b.value 0) (a.value i)
  rw [a.naturality (Fin.zero_le i), b.naturality (Fin.zero_le i)] at h
  exact h.symm

/-- 概要：plusの切れ目とminusの共有点も全頂点で一貫して比較できる。
方針：始頂点で比較し、Galois対応で全頂点へ移す。
規約：二種類の切れ目の向きの混在を除く。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionCut_mixed_total (a : WalkingAdjunctionPlusCut F)
    (b : WalkingAdjunctionMinusCut F) :
    (∀ i, (b.value i).val < (a.value i).val) ∨
      (∀ i, (a.value i).val ≤ (b.value i).val) := by
  by_cases h : (b.value 0).val < (a.value 0).val
  · exact Or.inl (fun i => (walkingAdjunctionCut_mixed_iff a b i).mpr h)
  · exact Or.inr (fun i => not_lt.mp
      (fun hi => h ((walkingAdjunctionCut_mixed_iff a b i).mp hi)))

end SerrePositivity.InfinityCategories.HA.Monads
