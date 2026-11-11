module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanFibrationTools
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementKanComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.KanComparisonFibers
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.KanEquivalencePaths
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanLimits

/-!
概要：Kan 複体間の区間の path 置換の終点射は Kan fibration で、二段の模型も Kan。
方針：可逆 path 置換との比較同型で相対充填性を移す。
規約：元の射に fibration 性は要求しない。
使われ方：filtered な path 引き戻しを空間の極限模型に接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange


/-- 概要：Kan 複体間の任意の射の区間の path 置換は終点へ Kan fibration を持つ。
方針：既存の可逆 path 置換の終点射を比較の逆同型で前合成する。
規約：元の f の fibration 性は不要。使われ方：二段目の引き戻しの Kan 性。 -/
instance intervalReplacementEndpoint_fibration {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) : Fibration (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f) := by
  have he : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f =
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.equivalenceIntervalReplacementIso f).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.equivalenceIntervalReplacementIso_endpoint, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  rw [he]
  infer_instance

/-- 概要：Kan 複体間の区間の path 置換も Kan 複体。
方針：可逆 path の始点評価の引き戻しの Kan 性を比較同型で移す。
規約：元の f の相対充填性は要求しない。使われ方：模型を Kan 対象に束ねる。 -/
instance intervalReplacement_kanComplex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacement f) := by
  have : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) := inferInstance
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement f) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pullback_kanComplex_of_fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0) f
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.equivalenceIntervalReplacementIso f)

/-- 概要：Kan 値の二射の二段の path 引き戻しは Kan 複体。
方針：path 置換の終点の fibration 性に沿って第二入力を引き戻す。
規約：両入力の射の fibration 性は不要。使われ方：homotopy pullback の Kan 模型。 -/
instance intervalPullback_kanComplex {X Y Z : SSet.{u}}
    [KanComplex X] [KanComplex Y] [KanComplex Z] (f : X ⟶ Y) (g : Z ⟶ Y) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback f g) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pullback_kanComplex_of_fibration (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f) g

end SerrePositivity.InfinityCategories.Project.FilteredExchange
