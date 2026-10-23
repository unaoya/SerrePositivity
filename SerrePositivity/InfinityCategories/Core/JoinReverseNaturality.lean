module
public import SerrePositivity.InfinityCategories.Core.JoinReverseEquiv
public import SerrePositivity.InfinityCategories.Core.JoinReverseIntervals

/-! # join の反転の自然性

概要：join の反転は単体作用と可換である。
方針：切断の補数と左右の区間の反転の式を使い、二つの因子を比較する。
規約：空次数を含む任意の有限順序写像。使われ方：S4 の join の反転同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：補った op の同値は異種等式を反映する。
方針：頂点数を置換して同値の単射性を使う。
規約：比較する頂点数は等しい。使われ方：反転した左右因子の自然性。 -/
lemma stableAugOpEquiv_heq (K : SSet.{u}) {r r' : ℕ} (hr : r = r')
    (x : Join.augObj K.op r) (y : Join.augObj K.op r')
    (h : HEq (stableAugOpEquiv K r x) (stableAugOpEquiv K r' y)) : HEq x y := by
  subst r'
  exact heq_of_eq ((stableAugOpEquiv K r).injective (eq_of_heq h))

/-- 概要：切断表示の反転は反転した順序写像の作用を元の順序写像の作用へ移す。
方針：切断を補数で比較し、左右の因子を op 前の区間の写像で比較する。
規約：α は空区間も含む任意の順序写像。使われ方：join の反転の自然性。 -/
lemma stableAugJoinReversePair_naturality (K L : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (s : StableAugJoin K L n) :
    stableAugJoinReversePairEquiv K L m (stableAugJoinMap K L (stableReverseOrderHom α) s) =
      stableAugJoinMap L.op K.op α (stableAugJoinReversePairEquiv K L n s) := by
  let a := s.1.val
  let t := stableAugJoinMap K L (stableReverseOrderHom α) s
  let a' := t.1.val
  have han : a ≤ n := Nat.le_of_lt_succ s.1.isLt
  have hcut := stablePullCut_reverse α a han
  have hbound := Join.pullCut_le α (n - a)
  have hc : m - a' = Join.pullCut α (n - a) := by
    change m - Join.pullCut (stableReverseOrderHom α) a = Join.pullCut α (n - a)
    omega
  refine stableAugJoin_hext _ _ hc ?_ ?_
  · change HEq (stableAugJoinReversePairEquiv K L m t).2.1
      (Join.augMap L.op (Join.leftMap α (n - a)) (stableAugJoinReversePairEquiv K L n s).2.1)
    apply stableAugOpEquiv_heq L hc
    rw [stableAugJoinReversePair_left, stableAugOpEquiv_naturality, stableAugJoinReversePair_left]
    apply stableAugMap_heq L hc rfl _ _ (stableReverseRightMap_val α a han) _ _ HEq.rfl
  · change HEq (stableAugJoinReversePairEquiv K L m t).2.2
      (Join.augMap K.op (Join.rightMap α (n - a)) (stableAugJoinReversePairEquiv K L n s).2.2)
    apply stableAugOpEquiv_heq K (congrArg (fun c ↦ m - c) hc)
    rw [stableAugJoinReversePair_right, stableAugOpEquiv_naturality, stableAugJoinReversePair_right]
    refine (cast_heq _ _).trans ?_
    apply stableAugMap_heq K hcut (by omega : a = n - (n - a)) _ _
      (stableReverseLeftMap_val α a han) _ _ (cast_heq _ _).symm

/-- 概要：join の反転の各次数の同値は単体作用と可換。
方針：op の自然性、join の切断表示の自然性、左右交換の自然性を合成する。
規約：全ての頂点数を許す。使われ方：反転を単体集合の射として束ねる。 -/
lemma stableAugJoinReverseEquiv_naturality (K L : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (s : Join.augObj (join K L).op n) :
    stableAugJoinReverseEquiv K L m (Join.augMap (join K L).op α s) =
      Join.augMap (join L.op K.op) α (stableAugJoinReverseEquiv K L n s) := by
  apply (stableAugJoinEquiv L.op K.op m).injective
  change (stableAugJoinEquiv L.op K.op m)
    ((stableAugJoinEquiv L.op K.op m).symm
      (stableAugJoinReversePairEquiv K L m
        (stableAugJoinEquiv K L m
          (stableAugOpEquiv (join K L) m (Join.augMap (join K L).op α s))))) = _
  rw [Equiv.apply_symm_apply, stableAugJoinEquiv_naturality L.op K.op]
  change _ = stableAugJoinMap L.op K.op α
    ((stableAugJoinEquiv L.op K.op n)
      ((stableAugJoinEquiv L.op K.op n).symm
        (stableAugJoinReversePairEquiv K L n
          (stableAugJoinEquiv K L n (stableAugOpEquiv (join K L) n s)))))
  rw [Equiv.apply_symm_apply, stableAugOpEquiv_naturality,
    stableAugJoinEquiv_naturality, stableAugJoinReversePair_naturality]

end SerrePositivity.InfinityCategories
