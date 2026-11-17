module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalRestriction
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrderProfiles
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionResidualObjects
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutRank

/-!
概要：二つの比較済みの切れ目の間へ、実単体の有限単調射を制限する。
方針：plusの逆像の条件とminusの共有点の条件から像の上下を証明する。
規約：上下の条件を追加の仮定にせず、切れ目の実データから供給する。
使われ方：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の残りの水平因子の全射。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {n : ℕ} {X Y M N : WalkingAdjunctionPoint}
  {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：切れ目の座標は、中点の補正を加えれば全体の点の個数以下。
方針：plusは隙間、minusは実点であることを使う。
規約：空の区間も含む。使われ方：Riehl–Verity Proposition 3.1.10 の区間の範囲。 -/
lemma walkingAdjunctionCut_bound (a : WalkingAdjunctionCut F M) (i : Fin (n + 1)) :
    walkingAdjunctionCutCoordinate a i + walkingAdjunctionTargetCorrection M ≤
      walkingAdjunctionOrdinalCard X Y (F.obj i) := by
  cases M
  · change (a.value i).val + 0 ≤ walkingAdjunctionOrdinalCard X Y (F.obj i)
    have hi := (a.value i).isLt
    omega
  · change (a.value i).val + 1 ≤ walkingAdjunctionOrdinalCard X Y (F.obj i)
    exact (a.value i).isLt

/-- 概要：切れ目の順位の比較は自然数の座標の比較を含む。
方針：中点の補正が0か1であることを使う。
規約：二種類の切れ目を含む。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionCutCoordinate_le (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N) (i : Fin (n + 1))
    (h : walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) :
    walkingAdjunctionCutCoordinate a i ≤ walkingAdjunctionCutCoordinate b i := by
  have hc : walkingAdjunctionTargetCorrection N ≤ 1 := by cases N <;> decide
  unfold walkingAdjunctionCutRank at h
  omega

/-- 概要：切れ目の右にある点の像も、対応する切れ目の右にある。
方針：plusは区間表示の逆像の判定、minusは共有点と単調性を使う。
規約：元の全単体の任意の射を扱う。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionCut_lower (a : WalkingAdjunctionCut F M) {i j : Fin (n + 1)}
    (h : i ≤ j) (k : Fin (walkingAdjunctionOrdinalCard X Y (F.obj i)))
    (hk : walkingAdjunctionCutCoordinate a i ≤ k.val) :
    walkingAdjunctionCutCoordinate a j ≤
      (walkingAdjunctionOrderHom (F.map (homOfLE h)) k).val := by
  cases M
  · have hc := ordinalIntervalMap_cut_iff
      (walkingAdjunctionOrderHom (F.map (homOfLE h))) k (a.value j)
    rw [a.naturality h] at hc
    change (a.value i).val ≤ k.val at hk
    change (a.value j).val ≤ _
    have hn : ¬ (walkingAdjunctionOrderHom (F.map (homOfLE h)) k).val < (a.value j).val :=
      fun hh => (not_lt_of_ge hk) (hc.mpr hh)
    omega
  · have hk' : a.value i ≤ k := hk
    have hl := (walkingAdjunctionOrderHom (F.map (homOfLE h))).monotone hk'
    rw [a.naturality h] at hl
    exact hl

/-- 概要：切れ目より前の区間の点の像は対応する区間内にある。
方針：plusは逆像の判定、minusは共有点と単調性を使う。
規約：minusの共有点を含む範囲。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionCut_upper (a : WalkingAdjunctionCut F M) {i j : Fin (n + 1)}
    (h : i ≤ j) (k : Fin (walkingAdjunctionOrdinalCard X Y (F.obj i)))
    (hk : k.val < walkingAdjunctionCutCoordinate a i + walkingAdjunctionTargetCorrection M) :
    (walkingAdjunctionOrderHom (F.map (homOfLE h)) k).val <
      walkingAdjunctionCutCoordinate a j + walkingAdjunctionTargetCorrection M := by
  cases M
  · have hc := ordinalIntervalMap_cut_iff
      (walkingAdjunctionOrderHom (F.map (homOfLE h))) k (a.value j)
    rw [a.naturality h] at hc
    exact hc.mp hk
  · have hk' : k ≤ a.value i := by
      change k.val < (a.value i).val + 1 at hk
      change k.val ≤ (a.value i).val
      omega
    have hu := (walkingAdjunctionOrderHom (F.map (homOfLE h))).monotone hk'
    rw [a.naturality h] at hu
    change (walkingAdjunctionOrderHom (F.map (homOfLE h)) k).val < (a.value j).val + 1
    change (walkingAdjunctionOrderHom (F.map (homOfLE h)) k).val ≤ (a.value j).val at hu
    omega

/-- 概要：二つの切れ目の間の点の個数。
方針：座標の差に終点の共有点の補正を加える。
規約：始点の種類も順位で別に保持する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
def walkingAdjunctionCutIntervalSize (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N) (i : Fin (n + 1)) : ℕ :=
  walkingAdjunctionCutCoordinate b i - walkingAdjunctionCutCoordinate a i +
    walkingAdjunctionTargetCorrection N

/-- 概要：比較済みの二つの切れ目の間の区間は全体の中に入る。
方針：座標の順序と、右端の切れ目の範囲を使う。
規約：空の区間も含む。使われ方：Riehl–Verity Proposition 3.1.10 の実包含。 -/
lemma walkingAdjunctionCutInterval_bound (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N) (i : Fin (n + 1))
    (h : walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) :
    walkingAdjunctionCutCoordinate a i + walkingAdjunctionCutIntervalSize a b i ≤
      walkingAdjunctionOrdinalCard X Y (F.obj i) := by
  have hab := walkingAdjunctionCutCoordinate_le a b i h
  have hb := walkingAdjunctionCut_bound b i
  unfold walkingAdjunctionCutIntervalSize
  omega

/-- 概要：比較済みの二つの切れ目の間の実有限単調射。
方針：元の射を区間へ制限し、像の上下の条件を二つの切れ目から供給する。
規約：上下の条件を仮定として追加しない。使われ方：Riehl–Verity Proposition 3.1.10。 -/
def walkingAdjunctionCutIntervalMap (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N)
    (h : ∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    Fin (walkingAdjunctionCutIntervalSize a b i) →o
      Fin (walkingAdjunctionCutIntervalSize a b j) :=
  ordinalRestrict (walkingAdjunctionOrderHom (F.map (homOfLE hij)))
    (walkingAdjunctionCutCoordinate a i) (walkingAdjunctionCutCoordinate a j)
    (walkingAdjunctionCutIntervalSize a b i) (walkingAdjunctionCutIntervalSize a b j)
    (walkingAdjunctionCutInterval_bound a b i (h i))
    (fun k => walkingAdjunctionCut_lower a hij _ (by
      change walkingAdjunctionCutCoordinate a i ≤ walkingAdjunctionCutCoordinate a i + k.val
      omega))
    (fun k => by
      have habi := walkingAdjunctionCutCoordinate_le a b i (h i)
      have habj := walkingAdjunctionCutCoordinate_le a b j (h j)
      have hk := k.isLt
      have hs : (ordinalSegmentInclusion _ _ _
          (walkingAdjunctionCutInterval_bound a b i (h i)) k).val <
          walkingAdjunctionCutCoordinate b i + walkingAdjunctionTargetCorrection N := by
        change walkingAdjunctionCutCoordinate a i + k.val < _
        unfold walkingAdjunctionCutIntervalSize at hk
        omega
      have hu := walkingAdjunctionCut_upper b hij _ hs
      have hsize : walkingAdjunctionCutCoordinate a j + walkingAdjunctionCutIntervalSize a b j =
          walkingAdjunctionCutCoordinate b j + walkingAdjunctionTargetCorrection N := by
        unfold walkingAdjunctionCutIntervalSize
        omega
      rw [hsize]
      exact hu)

end SerrePositivity.InfinityCategories.HA.Monads
