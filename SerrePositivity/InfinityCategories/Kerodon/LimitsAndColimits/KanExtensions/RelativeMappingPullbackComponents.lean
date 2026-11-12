module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeMappingPullback

/-!
概要：相対写像空間の引き戻し比較の両成分と元の図式の同定。
方針：相対内部 Hom の二つの射影と pinched 引き戻し同型の射影の式を読む。
規約：元の関手 F と G の制限・U 像を等式で回収する。
使われ方：Kerodon Proposition 7.3.6.7（Tag 030F） の四つの写像空間との厳密な接続。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：相対比較で写した関手頂点の第一成分は元の制限関手。
方針：相対内部 Hom の比較の第一射影を頂点で評価する。
規約：自然同型ではなく指定された頂点の等式。
使われ方：引き戻しの上側の写像空間の端点の同定。 -/
lemma kanRelativeMapping_sourceVertex {K C D E : SSet.{u}} (U : D ⟶ E) (δ : K ⟶ C)
    (s : internalHom.PullbackObjObj δ U) (F : C ⟶ D) :
    s.fst.app (Opposite.op ⦋0⦌) (s.π.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (δ ≫ F) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app s.π_fst (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)

/-- 概要：相対比較で写した関手頂点の第二成分は U による像。
方針：相対内部 Hom の比較の第二射影を頂点で評価する。
規約：元の底の図式を厳密に回収する。
使われ方：引き戻しの下側の写像空間の端点の同定。 -/
lemma kanRelativeMapping_baseVertex {K C D E : SSet.{u}} (U : D ⟶ E) (δ : K ⟶ C)
    (s : internalHom.PullbackObjObj δ U) (F : C ⟶ D) :
    s.snd.app (Opposite.op ⦋0⦌) (s.π.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ U) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app s.π_snd (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)

/-- 概要：写像空間の引き戻し比較の第一射影は元の相対制限の第一成分。
方針：引き戻し同型の第一射影の式を前合成する。
規約：全単体の射の等式。
使われ方：元の自然変換の制限として比較射を確認する。 -/
lemma kanRelativeMappingPullbackComparison_fst {K C D E : SSet.{u}}
    (U : D ⟶ E) (δ : K ⟶ C) (s : internalHom.PullbackObjObj δ U) (F G : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeMappingPullbackComparison U δ s F G ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap s.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap s.fst (s.π.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) (s.π.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeMappingPullbackComparison, Category.assoc]
  exact congrArg (fun k ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap s.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) ≫ k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHom_isPullback s.isPullback _ _).isoPullback_hom_fst

/-- 概要：写像空間の引き戻し比較の第二射影は元の相対制限の底の成分。
方針：引き戻し同型の第二射影の式を前合成する。
規約：全単体の射の等式。
使われ方：元の自然変換の U 像として比較射を確認する。 -/
lemma kanRelativeMappingPullbackComparison_snd {K C D E : SSet.{u}}
    (U : D ⟶ E) (δ : K ⟶ C) (s : internalHom.PullbackObjObj δ U) (F G : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeMappingPullbackComparison U δ s F G ≫ pullback.snd _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap s.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap s.snd (s.π.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) (s.π.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeMappingPullbackComparison, Category.assoc]
  exact congrArg (fun k ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap s.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) ≫ k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHom_isPullback s.isPullback _ _).isoPullback_hom_snd

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
