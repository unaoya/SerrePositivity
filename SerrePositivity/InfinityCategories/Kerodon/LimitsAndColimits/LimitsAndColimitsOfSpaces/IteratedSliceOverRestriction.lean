module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.IteratedSliceOverIso

/-!
概要：反復 slice の同型が、元の図式への制限と slice の射影を対応させることを示す。
方針：展開した図式を元の右因子へ制限し、外側二因子の包含の再結合を使う。
規約：同型は元の X への射影だけでなく sliceOver p への射も保つ。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS） の native な比較 span の始点評価の同定。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：固定図式の等式で slice の終域を移送しても族の uncurry は変わらない。
方針：図式の等式で置換して恒等射への後合成に戻す。
規約：図式の等式の証明への依存はない。
使われ方：Kerodon §4.3.6（Tag 018E） の図式への制限の固定条件の正規化。 -/
lemma sliceOverUncurry_eqToHom {K X A : SSet.{u}} {p r : K ⟶ X}
    (h : p = r) (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (s ≫ eqToHom (congrArg (fun f : K ⟶ X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver f) h)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry s := by
  cases h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (s ≫ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) = _
  rw [Category.comp_id]

variable {K L X A : SSet.{u}} {p : K ⟶ X} (q : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)

/-- 概要：展開した図式の slice を元の図式 p の slice へ制限する標準射。
方針：右因子 K への包含で制限し、展開した図式の固定条件で終域を同定する。
規約：終域は sliceOver p そのもの。
使われ方：HTT 4.2.4.1 の native な比較 span の始点評価の模型。 -/
def uncurriedSliceOverRestriction : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry q) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr L K) ≫
    eqToHom (congrArg (fun f : K ⟶ X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed q))

/-- 概要：元の図式への slice の制限を展開すると右因子の包含による前合成になる。
方針：終域の図式の移送を除き、slice の制限と uncurry の可換式を使う。
規約：任意のパラメータの族について述べる。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の反復 slice の射影との比較の計算。 -/
lemma uncurriedSliceOverRestriction_uncurry (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (s ≫ uncurriedSliceOverRestriction q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr L K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry s := by
  rw [uncurriedSliceOverRestriction, ← Category.assoc,
    sliceOverUncurry_eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed q),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_restrict]

/-- 概要：反復 slice の族を同型で移して制限すると元の slice の射影に一致する。
方針：uncurry で検出し、外側二因子の包含と結合同型の逆の可換式を使う。
規約：全パラメータでの実際の射の厳密な等式。
使われ方：HTT 4.2.4.1 の native な比較 span の評価の追跡。 -/
lemma iteratedSliceOverForwardFamily_restriction (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverForwardFamily q s ≫ uncurriedSliceOverRestriction q =
      s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection q := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective p
  rw [uncurriedSliceOverRestriction_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverForwardFamily_uncurry,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinAssociator_inv_outerPair, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection]

/-- 概要：反復 slice の厳密な同型は元の図式への制限と slice の射影を対応させる。
方針：恒等族における制限の公式を使う。
規約：終域は sliceOver p。単に X への射影の一致に弱めない。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の比較 span の二つの中間模型の実際の評価の同定。 -/
lemma iteratedSliceOverIso_restriction :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverIso q).hom ≫ uncurriedSliceOverRestriction q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection q := by
  simpa only [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverIso, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverMap] using
    iteratedSliceOverForwardFamily_restriction q (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q))

/-- 概要：展開した図式の slice から元の slice への制限は可変頂点の射影を保つ。
方針：反復 slice の同型の順方向で消去し、二つの射影の可換式を使う。
規約：図式・単体集合に充填性を仮定しない。
使われ方：HTT 4.2.4.1 の同じ底の頂点 fiber への比較 span の制限。 -/
lemma uncurriedSliceOverRestriction_projection :
    uncurriedSliceOverRestriction q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry q) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverIso q).hom).1
  rw [← Category.assoc, iteratedSliceOverIso_restriction]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.iteratedSliceOverIso_projection q).symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
