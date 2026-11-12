module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorOpposite

/-!
概要：quasicategory の同値を反転した単体集合の間の同値へ移す。
方針：同値の逆射を反転し、可逆二胞体の反転を逆向きに使う。
規約：始域と標的をともに反転する。
使われ方：coslice の局所 Kan 添字の比較を slice 側へ移送する。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：quasicategory の同値の反転の逆データ。
方針：二つの可逆二胞体を反転し、恒等射への向きを戻す。
規約：順方向は元の順方向の射の op。
使われ方：局所添字の反転による同値の移送。 -/
def qCatEquivalenceOpposite {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X.op Y.op where
  hom := SSet.opFunctor.map e.hom
  inv := SSet.opFunctor.map e.inv
  homInvIso := by
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoOpposite e.homInvIso).symm
  invHomIso := by
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoOpposite e.invHomIso).symm

/-- 概要：同値という性質も反転に保たれる。
方針：逆データを選んで反転する。
規約：同値の射は指定されたまま。
使われ方：右側の局所添字の比較から左側の比較を得る。 -/
lemma isQCatEquivalence_op {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (SSet.opFunctor.map f) :=
  (qCatEquivalenceOpposite h.choose).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
