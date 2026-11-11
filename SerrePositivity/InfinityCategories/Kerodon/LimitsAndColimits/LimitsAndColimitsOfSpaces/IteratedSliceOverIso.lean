module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.IteratedSliceOverFamilies
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

/-!
概要：反復 slice と展開した図式の slice の厳密な同型を構成する。
方針：任意の族の往復則とパラメータ自然性を恒等族に適用する。
規約：sliceOver q の固定図式 q は sliceOver p に値を持つ。充填性は不要。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS） の錐への射と錐の図式上の切断の比較。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

variable {K L X A : SSet.{u}} {p : K ⟶ X} (q : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)

/-- 概要：反復 slice と展開した図式の slice への任意の射は全単射で対応する。
方針：構成済みの二方向の族と厳密な往復則を束ねる。
規約：パラメータ A は任意の単体集合。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の native な錐の共通模型の普遍性。 -/
def iteratedSliceOverHomEquiv (A : SSet.{u}) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q) ≃ (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry q)) where
  toFun := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverForwardFamily q
  invFun := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverBackwardFamily q
  left_inv := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverFamily_backward_forward q
  right_inv := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverFamily_forward_backward q

/-- 概要：反復 slice から展開した図式の slice への標準射。
方針：反復 slice の普遍的な恒等族を二度展開して再結合する。
規約：同値の逆の選択を使わない。
使われ方：HTT 4.2.4.1 の実際の native な比較 span の移送。 -/
def iteratedSliceOverMap : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverForwardFamily q (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q))

/-- 概要：任意の族の順方向の比較は標準射への後合成に一致する。
方針：パラメータ自然性を恒等族に適用する。
規約：実際の構成済みの比較射を特定する。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の同型の順方向の評価と往復則。 -/
lemma iteratedSliceOverForwardFamily_eq (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverForwardFamily q s = s ≫ iteratedSliceOverMap q := by
  simpa only [Category.comp_id, iteratedSliceOverMap] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverForwardFamily_naturality q s (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q))

/-- 概要：展開した図式の slice から反復 slice への標準逆射。
方針：展開した図式の slice の恒等族を二度 curry する。
規約：順方向と同じ join の結合同型の逆関係を使う。
使われ方：HTT 4.2.4.1 の native な錐の共通模型の逆方向。 -/
def iteratedSliceOverInv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry q) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverBackwardFamily q (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry q)))

/-- 概要：任意の族の逆方向の比較は標準逆射への後合成に一致する。
方針：逆方向のパラメータ自然性を恒等族に適用する。
規約：逆射も恒等族から構成した実際の射。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の同型の両逆則。 -/
lemma iteratedSliceOverBackwardFamily_eq (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverBackwardFamily q s = s ≫ iteratedSliceOverInv q := by
  simpa only [Category.comp_id, iteratedSliceOverInv] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverBackwardFamily_naturality q s (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry q)))

/-- 概要：反復 slice は展開した固定図式の slice と単体集合として厳密に同型。
方針：二方向の標準射と、任意の族の自然性・往復則を使う。
規約：任意の K・L・X・p・q に対して成立する。Kan 性は仮定しない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS） の錐への射の共通模型の同定。 -/
def iteratedSliceOverIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry q) where
  hom := iteratedSliceOverMap q
  inv := iteratedSliceOverInv q
  hom_inv_id := by
    rw [← iteratedSliceOverBackwardFamily_eq]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverFamily_backward_forward q (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q))
  inv_hom_id := by
    rw [← iteratedSliceOverForwardFamily_eq]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverFamily_forward_backward q (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry q)))

/-- 概要：反復 slice の族の比較は二重の可変頂点の射影を保つ。
方針：順方向を展開し、最初の因子の包含と結合同型の可換式を使う。
規約：射影の保持は単体集合の射の厳密な等式。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の比較 span を同じ底の頂点 fiber へ移す準備。 -/
lemma iteratedSliceOverForwardFamily_projection (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverForwardFamily q s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry q) =
      s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverForwardFamily q s),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverForwardFamily_uncurry, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator_inv_first,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, Category.assoc]

/-- 概要：反復 slice の厳密な同型は元の X への二重の射影と可換。
方針：恒等族での射影の公式を使う。
規約：同型を頂点 fiber へ制限できるための底上の等式。
使われ方：HTT 4.2.4.1 の native な比較 span の中間空間の移送。 -/
lemma iteratedSliceOverIso_projection :
    (iteratedSliceOverIso q).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p := by
  simpa only [Category.id_comp, iteratedSliceOverIso, iteratedSliceOverMap] using
    iteratedSliceOverForwardFamily_projection q (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
