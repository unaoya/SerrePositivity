module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftFibrationHomReflection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IntervalCosliceSource
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TrivialFibrationCocone

/-!
概要：指定した全余錐比較の頂点射を保持し、可逆性と余極限性を移す。
方針：coslice 内の始対象の一意性と left fibration の可逆性反映を使う。
規約：同じ全余錐比較の射を全評価で使う。
使われ方：有限余積の全関手の指定比較と生成表示による検出。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の余錐比較から元の頂点間の射を取る。
方針：同じ coslice 射影をホモトピー圏で適用する。
規約：元の両余錐を保持する。
使われ方：指定比較の全パラメータの射。 -/
def nativeCoconeHomApex {K X : SSet.{u}} {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (α : (HomotopyCategory.mk c : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) ⟶ HomotopyCategory.mk d) :
    (HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ HomotopyCategory.mk d.vertex :=
  (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)).toFunctor.map α

/-- 概要：指定余錐比較を元の後合成で写す。
方針：coslice の後合成関手をホモトピー圏へ移す。
規約：比較の選び直しをしない。
使われ方：全関手の比較を各点で評価する。 -/
def nativeCoconeHomPostcomp {K X Y : SSet.{u}} {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (q : X ⟶ Y)
    (α : (HomotopyCategory.mk c : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) ⟶ HomotopyCategory.mk d) :
    (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q c) : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (p ≫ q))) ⟶
      HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q d) :=
  (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p q)).toFunctor.map α

/-- 概要：余錐比較の後合成と頂点射の後合成は一致する。
方針：元の coslice 後合成が射影を保つ等式を使う。
規約：同じ射の像を比較する。
使われ方：比較の各点での可逆性の判定。 -/
lemma nativeCoconeHomApex_postcomp {K X Y : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (q : X ⟶ Y)
    (α : (HomotopyCategory.mk c : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) ⟶ HomotopyCategory.mk d) :
    nativeCoconeHomApex (nativeCoconeHomPostcomp q α) =
      (hoFunctor.map q).toFunctor.map (nativeCoconeHomApex α) := by
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) c d α
  change SSet.Truncated.HomotopyCategory.homMk _ = SSet.Truncated.HomotopyCategory.homMk _
  congr 1

/-- 概要：二つの普遍余錐の間の指定比較は頂点で可逆。
方針：始対象間の射の可逆性を射影する。
規約：指定された比較射自身について結論する。
使われ方：Yoneda 像上の有限余積比較。 -/
lemma nativeCoconeHomApex_isIso {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p} (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d)
    (α : (HomotopyCategory.mk c : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) ⟶ HomotopyCategory.mk d) :
    IsIso (nativeCoconeHomApex α) := by
  have : IsIso α := isIso_of_isInitial hc.isInitialHo hd.isInitialHo α
  exact Functor.map_isIso _ α

/-- 概要：普遍余錐からの指定比較が頂点で可逆なら標的も普遍余錐。
方針：coslice 射影の可逆性反映から余錐全体の同型を得る。
規約：同じ比較射と全余錐を保つ。
使われ方：比較の全可逆性から有限余積保存へ戻す。 -/
lemma isColimitCone_of_nativeCoconeHomApex_isIso {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p} (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (α : (HomotopyCategory.mk c : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) ⟶ HomotopyCategory.mk d)
    (hα : IsIso (nativeCoconeHomApex α)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := by
  have : IsIso α := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftFibrationHom_isIso_of_map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) α hα
  exact hc.of_vertexIso (asIso α)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
