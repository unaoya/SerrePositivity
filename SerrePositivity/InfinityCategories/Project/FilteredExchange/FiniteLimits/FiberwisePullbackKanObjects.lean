module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackKanComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.KanIntervalPullbackTransport

/-!
概要：全空間 Kan 引き戻し比較の両対象と射を、元の台のまま Kan 対象に束ねる。
方針：具体的な Kan 置換と既存の区間引き戻し Kan 対象を使う。
規約：元の比較射を変更しない。使われ方：𝒮 内の比較辺と極限錐。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：具体的 Kan 置換を元の宇宙の Kan 対象に束ねる。
方針：構成済みの充填性。規約：台は元の Q。使われ方：全空間余極限頂点の cospan。 -/
def continuousKanObject (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj X, inferInstance⟩

/-- 概要：元の射の具体的な Kan 置換を Kan 対象の射に束ねる。
方針：台の射をそのまま使う。規約：単位との自然性を保持。使われ方：元の cospan。 -/
def continuousKanMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    continuousKanObject X ⟶ continuousKanObject Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f

/-- 概要：元の fiber ごとの引き戻し全空間の Kan 対象。
方針：元の全空間を Q で置換。規約：元の台。使われ方：輸送後の極限錐の頂点。 -/
def fiberwisePullbackTotalKanObject {E D H B : SSet.{u}}
    (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  continuousKanObject (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g)

/-- 概要：三全空間の Kan 置換の path 引き戻し対象。
方針：元の任意の二射の区間引き戻し。規約：追加の fibration 仮定なし。使われ方：元の極限錐。 -/
def fiberwisePullbackTargetKanObject {E D H : SSet.{u}} (f : E ⟶ H) (g : D ⟶ H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackKanObject (continuousKanMap f) (continuousKanMap g)

/-- 概要：実際の全空間引き戻し比較を元の Kan 対象間の射として表示する。
方針：台の比較をそのまま使う。規約：三射影・単位を保持。使われ方：native な比較辺。 -/
def fiberwisePullbackComparisonKanMap {E D H B : SSet.{u}}
    (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) :
    fiberwisePullbackTotalKanObject p f g ⟶ fiberwisePullbackTargetKanObject f g :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison p f g

end SerrePositivity.InfinityCategories.Project.FilteredExchange
