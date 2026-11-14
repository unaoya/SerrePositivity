module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.HornPointJoin
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensor
public import SerrePositivity.InfinityCategories.HTT.Section2_1_3.WeakContractibility
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：Kan 複体では filtered 性と可縮 Kan 性が一致する。
方針：境界の余錐を最後のホーンと同定し、Kan 充填の底面を取り出す。
規約：一般の filtered ∞ 圏に Kan 性や全境界の充填を要求しない。
使われ方：filtered な空間の可縮性と cofinality の補助判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：filtered な Kan 複体では全ての境界が充填できる。
方針：有限境界の余錐を最後のホーンとして充填し、その底の面に制限する。
規約：Kan 性を明示的に仮定する。
使われ方：filtered 空間の可縮性。 -/
lemma isContractibleKan_of_isFilteredInfinity (C : SSet.{u}) [KanComplex C]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan C := by
  intro n b
  obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity.cocone_nonempty b
  obtain ⟨F, hF⟩ := KanComplex.hornFilling ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.finalHornPointJoinIso n).inv ≫ c.val)
  have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (boundary n).ι (𝟙 Δ[0]) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ F = c.val := by
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.finalHornPointJoinIso_hom_ι, Category.assoc, ← hF]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.finalHornPointJoinIso n).hom_inv_id_assoc c.val
  refine ⟨stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n) ≫ F, ?_⟩
  calc
    (boundary n).ι ≫ stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n) ≫ F =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (boundary n : SSet.{u}) Δ[0] ≫ c.val := by
      rw [← hG]
      simp only [← Category.assoc]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap]
      simp only [Category.assoc]
      rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inl]
    _ = b := c.property

/-- 概要：可縮 Kan な ∞ 圏は filtered。
方針：一点への trivial Kan fibration に沿って図式を join へ延長する。
規約：この方向は有限性を使わず任意形状の余錐を作る。
使われ方：filtered 性の基本例と Kan 複体における逆方向。 -/
lemma isFilteredInfinity_of_isContractibleKan {C : SSet.{u}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C := by
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration C).1 hC
  constructor
  intro K _ f
  have := ht.mem (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]) inferInstance
  have sq : CommSq f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]) (terminal.from C) (terminal.from _) :=
    ⟨terminal.hom_ext _ _⟩
  exact ⟨⟨sq.lift, sq.fac_left⟩⟩

/-- 概要：Kan 複体の filtered 性と可縮 Kan 性は同値。
方針：最後のホーンによる必要性と trivial Kan fibration による十分性を合成する。
規約：一般の quasicategory の filtered 性を置き換える定義ではない。
使われ方：filtered な Kan 添字の可縮性の判定。 -/
@[kerodon 02PL]
lemma isFilteredInfinity_iff_isContractibleKan (C : SSet.{u}) [KanComplex C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan C := by
  constructor
  · intro h
    exact isContractibleKan_of_isFilteredInfinity C
  · exact isFilteredInfinity_of_isContractibleKan

/-- 概要：filtered な Kan 複体は弱可縮。
方針：証明した全境界充填から既存の弱可縮性へ接続する。
規約：Kan 性はこの補題の仮定。使われ方：空間を添字とする cofinality。 -/
lemma isWeaklyContractible_of_isFilteredKan (C : SSet.{u}) [KanComplex C]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C] : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible C :=
  (isContractibleKan_of_isFilteredInfinity C).isWeaklyContractible

end SerrePositivity.InfinityCategories.F2
