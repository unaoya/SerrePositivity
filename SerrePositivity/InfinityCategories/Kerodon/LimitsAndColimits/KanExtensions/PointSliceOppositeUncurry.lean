module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceOppositeUncurry
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenASliceOpposite

/-!
概要：頂点の標準表示へ正規化した slice の反転も普遍錐の展開を保つ。
方針：固定図式の等式による移送を消し、coslice の制限と反転の展開を合成する。
規約：Δ⁰.op から Δ⁰ への正規化を明示する。
使われ方：局所 Kan 添字の反転比較が標準指定変換を表すことの証明。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：固定図式の等式で coslice を移しても普遍錐の射は変わらない。
方針：等式について帰納する。
規約：底上の対象の等式による射の左成分を扱う。
使われ方：点の反転同型の正規化の最後の移送を消去する。 -/
lemma kanSliceUnderUncurry_eqToHom {A K X : SSet.{u}} {p q : K ⟶ X} (h : p = q)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (f ≫ (eqToHom
      (congrArg (fun r ↦ Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection r)) h)).left) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f := by
  subst q
  rfl

/-- 概要：頂点の slice の正規化した反転は元の普遍余錐の反転を表す。
方針：固定図式の移送を消去し、固定因子の制限と一般の反転の展開を計算する。
規約：任意のパラメータ A。
使われ方：slice の標準変換と反転した coslice の標準変換の同定。 -/
lemma kanPointSliceOverOpIso_uncurry {A X : SSet.{u}} (x : X _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (SSet.opFunctor.map f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso x).hom.left) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 A.op) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso A Δ[0]).inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso, Iso.trans_hom, Over.comp_left,
    Over.isoMk_hom_left]
  rw [eqToIso.hom]
  simp only [Over.isoMk_hom_left, asIso_hom]
  rw [← Category.assoc, ← Category.assoc, kanSliceUnderUncurry_eqToHom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverOpIso_uncurry]
  apply SSet.yonedaEquiv.injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseSimplex_yoneda, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
