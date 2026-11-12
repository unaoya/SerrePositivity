module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrecompositionTranspose
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom

/-!
概要：元の指定単位から、右・左関手による前合成の指定単位を構成する。
方針：豊穣前合成に元の実単位辺を写し、恒等と合成の端点を正規化する。
規約：この段階では前合成の随伴性を仮定しない。
使われ方：左射影の普遍単位模型に必要な前合成の全 QCat 随伴の単位候補。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：恒等関手による前合成は元の内部 Hom の恒等射。
方針：閉構造の前合成の恒等則を評価する。
規約：全ての単体集合に充填性を要求しない。
使われ方：前合成の単位辺の始点の正規化。 -/
lemma precomposition_identity (C Z : SSet.{u}) :
    (pre (𝟙 C)).app Z = 𝟙 ((ihom C).obj Z) :=
  NatTrans.congr_app (pre_id C) Z

/-- 概要：合成関手による前合成は逆順の二つの前合成。
方針：閉構造の前合成の合成則を評価する。
規約：単体集合の射の厳密な等式。
使われ方：前合成の単位辺の終点の正規化。 -/
lemma precomposition_composite {C D E : SSet.{u}} (L : C ⟶ D) (R : D ⟶ E) (Z : SSet.{u}) :
    (pre (L ≫ R)).app Z = (pre R).app Z ≫ (pre L).app Z :=
  NatTrans.congr_app (pre_map L R) Z

/-- 概要：元の実単位から前合成の指定単位の辺を作る。
方針：豊穣前合成の実際の辺を、恒等・合成の公式で両端だけ正規化する。
規約：元の単位の像の一次単体を変更しない。
使われ方：前合成の QCat 随伴の指定単位。 -/
def precompositionUnitEdge {C D : SSet.{u}} {L : C ⟶ D} {R : D ⟶ C}
    (H : SSet.Homotopy (𝟙 C) (L ≫ R)) (Z : SSet.{u}) :
    SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom ((ihom C).obj Z)).obj ((ihom C).obj Z)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 ((ihom C).obj Z)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((pre R).app Z ≫ (pre L).app Z)) where
  edge := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionHomotopyEdge H Z).edge
  src_eq := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionHomotopyEdge H Z).src_eq.trans
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (precomposition_identity C Z))
  tgt_eq := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precompositionHomotopyEdge H Z).tgt_eq.trans
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (precomposition_composite L R Z))

/-- 概要：元の実単位から前合成の h Fun の指定単位を作る。
方針：正規化した同じ辺の Hom 類を取る。
規約：前合成の随伴性はこの定義では要求しない。
使われ方：全パラメータの単位 Hom 判定への入力。 -/
def precompositionUnitHom {C D : SSet.{u}} {L : C ⟶ D} {R : D ⟶ C}
    (H : SSet.Homotopy (𝟙 C) (L ≫ R)) (Z : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 ((ihom C).obj Z)) ((pre R).app Z ≫ (pre L).app Z) :=
  SSet.Truncated.HomotopyCategory.homMk (precompositionUnitEdge H Z)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
