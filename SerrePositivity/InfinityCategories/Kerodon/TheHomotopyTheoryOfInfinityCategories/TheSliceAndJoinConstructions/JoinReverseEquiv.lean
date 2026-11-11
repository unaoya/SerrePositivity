module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinReverseCuts
public import Mathlib.Logic.Equiv.Prod

/-! # join の反転の各次数の同値

概要：join 全体を反転すると、左右の因子を交換してそれぞれを反転した join になる。
方針：切断を全頂点数から引き、左右の補った単体を交換する。
規約：空次数を含む。使われ方：S4 の slice／coslice の双対比較。

対応節は Kerodon 4.3（Tag 015M）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：全頂点数から切断を引く添字の同値。
方針：範囲内では二度引くと元の切断になることを使う。
規約：切断零と全区間を交換する。使われ方：join の反転。 -/
def stableComplementCutEquiv (r : ℕ) : Fin (r + 1) ≃ Fin (r + 1) where
  toFun a := ⟨r - a.val, by omega⟩
  invFun a := ⟨r - a.val, by omega⟩
  left_inv a := Fin.ext (by change r - (r - a.val) = a.val; have := a.isLt; omega)
  right_inv a := Fin.ext (by change r - (r - a.val) = a.val; have := a.isLt; omega)

/-- 概要：切断の反転に合わせて左右の因子を交換し、両因子を反転する。
方針：直積の交換と op の各次数の同値、第二因子の頂点数の移送を合成する。
規約：切断ごとの型の同値。使われ方：反転の再添字付けの fiber。 -/
def stableAugJoinReverseFiberEquiv (K L : SSet.{u}) (r : ℕ) (a : Fin (r + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K a.val × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj L (r - a.val)) ≃
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj L.op (stableComplementCutEquiv r a).val ×
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K.op (r - (stableComplementCutEquiv r a).val)) :=
  (Equiv.prodComm _ _).trans
    (Equiv.prodCongr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugOpEquiv L (r - a.val)).symm
      ((Equiv.cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K) (by
        have := a.isLt
        omega))).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugOpEquiv K (r - (r - a.val))).symm))

/-- 概要：join の切断表示を反転した二因子の切断表示へ移す同値。
方針：切断の補数と各 fiber の同値を直和で束ねる。
規約：各頂点数の同値。使われ方：反転の単体的な自然性。 -/
def stableAugJoinReversePairEquiv (K L : SSet.{u}) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.StableAugJoin K L r ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.StableAugJoin L.op K.op r :=
  Equiv.sigmaCongr (stableComplementCutEquiv r) (stableAugJoinReverseFiberEquiv K L r)

/-- 概要：join の反転後の切断位置は元の切断の補数。
方針：直和の同値の順方向を計算する。
規約：値は頂点数。使われ方：反転の自然性の切断部分。 -/
lemma stableAugJoinReversePair_cut (K L : SSet.{u}) (r : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.StableAugJoin K L r) :
    (stableAugJoinReversePairEquiv K L r s).1.val = r - s.1.val := rfl

/-- 概要：反転後の左因子を op 前の単体として読むと元の右因子になる。
方針：op の同値の右逆則を使う。
規約：左因子の頂点数は r から元の切断を引いたもの。
使われ方：join の反転の自然性の第一因子。 -/
lemma stableAugJoinReversePair_left (K L : SSet.{u}) (r : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.StableAugJoin K L r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugOpEquiv L (r - s.1.val) (stableAugJoinReversePairEquiv K L r s).2.1 = s.2.2 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugOpEquiv L _).apply_symm_apply _

/-- 概要：反転後の右因子を op 前の単体として読むと元の左因子の移送になる。
方針：op の同値の右逆則を使う。
規約：頂点数は r-(r-a)。使われ方：反転の自然性の第二因子。 -/
lemma stableAugJoinReversePair_right (K L : SSet.{u}) (r : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.StableAugJoin K L r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugOpEquiv K (r - (r - s.1.val)) (stableAugJoinReversePairEquiv K L r s).2.2 =
      cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K) (by have := s.1.isLt; omega :
        s.1.val = r - (r - s.1.val))) s.2.1 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugOpEquiv K _).apply_symm_apply _

/-- 概要：join 全体の反転と、因子を交換して反転した join の補った各次数は同値。
方針：op と join の切断表示の同値を挟んで反転する。
規約：自然性は別途必要。使われ方：join の反転の単体集合の同型。 -/
def stableAugJoinReverseEquiv (K L : SSet.{u}) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L).op r ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L.op K.op) r :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugOpEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L) r).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinEquiv K L r).trans
      ((stableAugJoinReversePairEquiv K L r).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinEquiv L.op K.op r).symm))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
