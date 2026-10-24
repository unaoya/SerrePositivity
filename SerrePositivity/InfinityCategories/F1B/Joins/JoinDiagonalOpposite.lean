module

public import SerrePositivity.InfinityCategories.F1B.Joins.JoinShiftCoefficient
public import SerrePositivity.InfinityCategories.Core.JoinReverseBoundary
public import SerrePositivity.InfinityCategories.Core.PrismOpposite

/-!
概要：join の区間付き対角と反転の両立。
方針：切断を補数に移し、先頭と末尾の制限を交換する。
規約：区間と係数をともに反転し、join の二因子を交換する。
使われ方：右 Kan 拡張の相対 join 表示を左側の一般の比較から導く。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：先頭の包含を反転すると補数の長さの末尾包含になる。
方針：有限順序集合の反転した添字を自然数として計算する。
規約：空区間を含む。
使われ方：区間付き対角の反転の左因子。 -/
lemma join_reverse_prefix (r k : ℕ) (hk : k ≤ r) :
    stableReverseOrderHom (Join.prefixIncl r (r - k) (by omega)) =
      Join.suffixIncl r k hk := by
  ext i
  simp only [stableReverseOrderHom, Join.prefixIncl, Join.suffixIncl]
  change r - (r - k - (i.val + 1) + 1) = k + i.val
  have := i.isLt
  omega

/-- 概要：二分した単体を反転すると補数で二分した反転単体になる。
方針：join の反転の二因子を復号し、補った op の自然性で比較する。
規約：空次数と頂点数の移送を含む。
使われ方：join の対角の反転の全単体での検証。 -/
lemma augJoinSplit_reverse (K : SSet.{u}) (r k : ℕ) (hk : k ≤ r)
    (a : Join.augObj K r) :
    let s : StableAugJoin K K r :=
      ⟨⟨k, by omega⟩, Join.augMap K (Join.prefixIncl r k hk) a,
        Join.augMap K (Join.suffixIncl r k hk) a⟩
    let a' := (stableAugOpEquiv K r).symm a
    stableAugJoinReversePairEquiv K K r s =
      ⟨⟨r - k, by omega⟩, Join.augMap K.op (Join.prefixIncl r (r - k) (by omega)) a',
        Join.augMap K.op (Join.suffixIncl r (r - k) (by omega)) a'⟩ := by
  intro s a'
  apply stableAugJoin_hext
  · rfl
  · apply stableAugOpEquiv_heq K rfl
    change HEq (stableAugOpEquiv K (r - k) (stableAugJoinReversePairEquiv K K r s).2.1)
      (stableAugOpEquiv K (r - k)
        (Join.augMap K.op (Join.prefixIncl r (r - k) (by omega)) a'))
    rw [stableAugJoinReversePair_left K K r s, stableAugOpEquiv_naturality,
      Equiv.apply_symm_apply, join_reverse_prefix]
  · apply stableAugOpEquiv_heq K rfl
    change HEq
      (stableAugOpEquiv K (r - (r - k)) (stableAugJoinReversePairEquiv K K r s).2.2)
      (stableAugOpEquiv K (r - (r - k))
        (Join.augMap K.op (Join.suffixIncl r (r - k) (by omega)) a'))
    rw [stableAugJoinReversePair_right K K r s, stableAugOpEquiv_naturality,
      Equiv.apply_symm_apply]
    refine (cast_heq _ _).trans ?_
    exact stableAugMap_heq K (by omega : k = r - (r - k)) rfl
      (Join.prefixIncl r k hk)
      (stableReverseOrderHom (Join.suffixIncl r (r - k) (by omega))) (by
        intro i j hij
        simp only [Join.prefixIncl, stableReverseOrderHom, Join.suffixIncl]
        change i.val = r - (r - k + (r - (r - k) - (j.val + 1)) + 1)
        have := i.isLt
        have := j.isLt
        omega) a a HEq.rfl

/-- 概要：区間の単体を反転すると値零の逆像の切断は補数になる。
方針：区間を二点の join に戻し、有限順序写像の反転した切断を使う。
規約：区間の反転は標準単体の op 同型の逆。
使われ方：対角の反転の切断の同定。 -/
lemma join_interval_cut_reverse (n : ℕ) (t : (Δ[1] : SSet.{u}) _⦋n⦌) :
    let τ := SSet.opObjEquiv ((stdSimplex.opIso ⦋1⦌).inv.app (Opposite.op ⦋n⦌) t)
    ((joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) τ).1.val =
      n + 1 - ((joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) t).1.val := by
  intro τ
  rw [intervalJoin_cut, intervalJoin_cut]
  change Join.pullCut (stableReverseOrderHom (stdSimplex.objEquiv t).toOrderHom) 1 = _
  exact stablePullCut_reverse (stdSimplex.objEquiv t).toOrderHom 1 (by decide)

/-- 概要：区間付き対角を反転し join の因子を交換すると反対側の対角になる。
方針：全単体で対角の二分とその反転を計算し、切断の補数を同定する。
規約：区間の両端も交換する。
使われ方：relative join の反転同型を pullback に持ち上げる可換性。 -/
lemma joinDiagonal_reverse (K : SSet.{u}) :
    reversePrism (joinDiagonal K) ≫ (stableJoinReverseIso K K).hom = joinDiagonal K.op := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, a⟩
  let τ := SSet.opObjEquiv ((stdSimplex.opIso ⦋1⦌).inv.app (Opposite.op ⦋n⦌) t)
  let a₀ := SSet.opObjEquiv a
  let s := (joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) τ
  let z := (joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) t
  have hs : s.1.val = n + 1 - z.1.val := join_interval_cut_reverse n t
  have hz : z.1.val ≤ n + 1 := Nat.le_of_lt_succ z.1.isLt
  have hc : n + 1 - s.1.val = z.1.val := by omega
  change stableAugJoinReversePairEquiv K K (n + 1)
      ((joinCylinderMap K K).app (Opposite.op ⦋n⦌) ((a₀, τ), a₀)) =
    (joinCylinderMap K.op K.op).app (Opposite.op ⦋n⦌) ((a, t), a)
  rw [joinCylinderMap_app, joinCylinderMap_app]
  rw [augJoinSplit_reverse K (n + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt) a₀]
  apply stableAugJoin_hext
  · exact hc
  · exact stableAugMap_heq K.op hc rfl
      (Join.prefixIncl (n + 1) (n + 1 - s.1.val) (by omega))
      (Join.prefixIncl (n + 1) z.1.val hz) (by intro i j hij; exact hij) a a HEq.rfl
  · exact stableAugMap_heq K.op (congrArg (fun k ↦ n + 1 - k) hc) rfl
      (Join.suffixIncl (n + 1) (n + 1 - s.1.val) (by omega))
      (Join.suffixIncl (n + 1) z.1.val hz) (by
        intro i j hij
        change n + 1 - s.1.val + i.val = z.1.val + j.val
        omega) a a HEq.rfl

end SerrePositivity.InfinityCategories
