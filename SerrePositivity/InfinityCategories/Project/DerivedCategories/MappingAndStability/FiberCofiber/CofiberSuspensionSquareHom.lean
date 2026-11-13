module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.CofiberSuspensionComparisonData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexSquareMiddleHomotopy
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.HomotopyEvaluationClass
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyEndpointTransport

/-! # 標準 cofiber から標準 suspension への四角形比較

概要：cone 写像への後合成と中間対象の零への変更を、四角形関手圏の h の射として合成する。
方針：変更後の全データの同定でホモトピーの終端を標準 suspension に合わせる。
規約：実際のホモトピーを保持する。使われ方：D7 の接続射の選択との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial ZeroObject
variable {S : Type u} [CommRing S] {A B : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 終点への後合成後に中間対象を零に送る、実際の四角形ホモトピー。 -/
def cofiberToSuspensionMiddleHomotopy (f : A ⟶ B) : SSet.Homotopy (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData f (0 : A ⟶ 0)).postcompose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)).square
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData (0 : A ⟶ 0) (0 : A ⟶ 0)).square :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homotopyOfEndpoints
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData f (0 : A ⟶ 0)).postcompose
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)).changeBottomMiddleHomotopy (0 : B ⟶ 0)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB (0 : A ⟶ 0) (0 : A ⟶ 0)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionRightFactor f)) rfl
    (congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData A 0 0
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutCofiber (0 : A ⟶ 0) (0 : A ⟶ 0)) => k.square)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionIntermediateData_eq f))

/-- 全複体の dg nerve における cofiber から suspension への四角形比較射。 -/
def cofiberToSuspensionSquareHom (f : A ⟶ B) :
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData f (0 : A ⟶ 0)).square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)))) ⟶
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData (0 : A ⟶ 0) (0 : A ⟶ 0)).square) :=
  SSet.Truncated.HomotopyCategory.homMk
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData f (0 : A ⟶ 0)).postcomposeSquareEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)) ≫
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (cofiberToSuspensionMiddleHomotopy f))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
