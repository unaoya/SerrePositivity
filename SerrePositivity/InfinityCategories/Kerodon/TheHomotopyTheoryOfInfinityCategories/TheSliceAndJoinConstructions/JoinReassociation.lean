module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinAugmented
public import Mathlib.Logic.Equiv.Prod

/-! # 補った join の三因子の組み替え

概要：三因子の join の切断表示を組み替える。
方針：切断の添字の同値と、その各因子の同値を直和・直積の同値で組み立てる。
規約：全ての因子の空単体を許す。使われ方：S4 の二重 coslice の比較。

対応節は Kerodon 4.3（Tag 015M）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：三因子の二つの切断を別の括弧の切断へ移す添字の同値。
方針：全体の前半の長さ b とその中の長さ a を、a と b-a へ写す。
規約：頂点数零も含む。使われ方：join の結合の再添字付け。 -/
def stableJoinCutEquiv (r : ℕ) :
    (Σ b : Fin (r + 1), Fin (b.val + 1)) ≃
      (Σ a : Fin (r + 1), Fin (r - a.val + 1)) where
  toFun s := ⟨⟨s.2.val, by have := s.1.isLt; have := s.2.isLt; omega⟩,
    ⟨s.1.val - s.2.val, by
      change s.1.val - s.2.val < r - s.2.val + 1
      have := s.1.isLt; have := s.2.isLt; omega⟩⟩
  invFun s := ⟨⟨s.1.val + s.2.val, by have := s.1.isLt; have := s.2.isLt; omega⟩,
    ⟨s.1.val, by change s.1.val < s.1.val + s.2.val + 1; omega⟩⟩
  left_inv := by
    rintro ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
    change a < b + 1 at ha
    have h : a + (b - a) = b := by omega
    dsimp only
    apply Sigma.ext (Fin.ext h)
    exact (Fin.heq_ext_iff (congrArg (fun n ↦ n + 1) h)).mpr rfl
  right_inv := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    dsimp only
    exact congrArg (fun i : Fin (r - a + 1) ↦
      (⟨(⟨a, ha⟩ : Fin (r + 1)), i⟩ : Σ a : Fin (r + 1), Fin (r - a.val + 1)))
      (Fin.ext (Nat.add_sub_cancel_left a b))

/-- 概要：直積の右因子にある直和を外へ出す同値。
方針：添字を移し、残る二成分を保つ。
規約：依存する右因子を許す。使われ方：右に括弧を付けた join の切断表示。 -/
def stableProdSigmaEquiv (A : Type u) (I : Type v) (B : I → Type w) :
    A × (Σ i, B i) ≃ Σ i, A × B i where
  toFun s := ⟨s.2.1, s.1, s.2.2⟩
  invFun s := ⟨s.2.1, s.1, s.2.2⟩

/-- 概要：左に括弧を付けた join の切断表示を二つの切断で展開する同値。
方針：内側の join の同値を適用し、直和と直積を分配して添字を束ねる。
規約：因子の順番は K、L、M。使われ方：結合の組み替えの始域。 -/
def stableAugJoinLeftTripleEquiv (K L M : SSet.{u}) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.StableAugJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L) M r ≃
      Σ s : (Σ b : Fin (r + 1), Fin (b.val + 1)),
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K s.2.val × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj L (s.1.val - s.2.val)) ×
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj M (r - s.1.val) :=
  (Equiv.sigmaCongrRight fun b : Fin (r + 1) ↦
    (Equiv.prodCongr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinEquiv K L b.val) (Equiv.refl _)).trans
      (Equiv.sigmaProdDistrib _ _)).trans (Equiv.sigmaAssoc _).symm

/-- 概要：右に括弧を付けた join の切断表示を二つの切断で展開する同値。
方針：内側の join を展開し、直和を外へ出して添字を束ねる。
規約：因子の順番は K、L、M。使われ方：結合の組み替えの終域。 -/
def stableAugJoinRightTripleEquiv (K L M : SSet.{u}) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.StableAugJoin K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L M) r ≃
      Σ s : (Σ a : Fin (r + 1), Fin (r - a.val + 1)),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K s.1.val × (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj L s.2.val ×
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj M (r - s.1.val - s.2.val)) :=
  (Equiv.sigmaCongrRight fun a : Fin (r + 1) ↦
    (Equiv.prodCongr (Equiv.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinEquiv L M (r - a.val))).trans
      (stableProdSigmaEquiv _ _ _)).trans (Equiv.sigmaAssoc _).symm

/-- 概要：三因子の切断の再添字付けは各因子の型の同値も伴う。
方針：直積を組み替え、最後の因子の頂点数の等式で移送する。
規約：最初の二因子の単体を保つ。使われ方：結合の組み替えの fiber。 -/
def stableJoinCutFiberEquiv (K L M : SSet.{u}) (r : ℕ)
    (s : Σ b : Fin (r + 1), Fin (b.val + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K s.2.val × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj L (s.1.val - s.2.val)) ×
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj M (r - s.1.val)) ≃
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K (stableJoinCutEquiv r s).1.val ×
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj L (stableJoinCutEquiv r s).2.val ×
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj M (r - (stableJoinCutEquiv r s).1.val -
          (stableJoinCutEquiv r s).2.val))) :=
  (Equiv.prodAssoc _ _ _).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
      (Equiv.cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj M) (by
        have := s.1.isLt; have := s.2.isLt
        change r - s.1.val = r - s.2.val - (s.1.val - s.2.val)
        omega)))))

/-- 概要：三因子の補った join の二つの括弧の切断表示は同値。
方針：両側を二つの切断に展開し、添字と各因子の同値を合成する。
規約：この段階では頂点数ごとの同値。使われ方：join の結合同型。 -/
def stableAugReassociationEquiv (K L M : SSet.{u}) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.StableAugJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L) M r ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.StableAugJoin K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L M) r :=
  (stableAugJoinLeftTripleEquiv K L M r).trans
    ((Equiv.sigmaCongr (stableJoinCutEquiv r) (stableJoinCutFiberEquiv K L M r)).trans
      (stableAugJoinRightTripleEquiv K L M r).symm)

/-- 概要：三因子の join の補った各次数で二つの括弧の表示は同値。
方針：既存の単体の表示を切断表示へ移し、切断の組み替えを挟んで戻す。
規約：自然性は別途必要な、頂点数ごとの同値。
使われ方：join の単体集合としての結合同型の構成。 -/
def stableAugJoinAssociatorEquiv (K L M : SSet.{u}) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L) M) r ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L M)) r :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L) M r).trans
    ((stableAugReassociationEquiv K L M r).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableAugJoinEquiv K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L M) r).symm)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
