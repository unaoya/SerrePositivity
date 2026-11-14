module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CommaSectionFiber
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaUnitComponent
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UniversalUnitComma

/-!
概要：選び直した単位の comma 頂点の元の辺と、その Hom 類を照合する。
方針：二重 fiber の回収公式と、元の単位ホモトピーの持ち上げの往復を使う。
規約：単位の代表の選択を変更しない。使われ方：始対象性の代表不変性への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 指定単位の comma 頂点を、元の F(x) 上の二重 fiber の点として保持。 -/
def unitCommaSectionTargetFiberVertex {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x)
      (F.app (Opposite.op ⦋0⦌) x)) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex η x, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection_target η) (Opposite.op ⦋0⦌)) x⟩

/-- 二重 fiber の指定単位から回収する辺は、同じ選んだホモトピーの頂点辺。 -/
lemma unitCommaSectionTargetFiberArrow_eq {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaTargetFiberArrow G x (F.app (Opposite.op ⦋0⦌) x)
      (unitCommaSectionTargetFiberVertex η x) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η) x := by
  apply SSet.Edge.ext
  have he := congrArg SSet.Edge.edge
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaSectionTargetFiberArrow_eq G (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection η) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSection_source η) x)
  change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaTargetFiberArrow G x (F.app (Opposite.op ⦋0⦌) x)
    (unitCommaSectionTargetFiberVertex η x)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift G (𝟙 X) F (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η))).h.app
        (Opposite.op ⦋1⦌)
        ((Truncated.Edge.id (X := (truncation 2).obj X) x).edge,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_homotopy_h] at he
  exact he

/-- 指定単位の二重 fiber の矢印の類は、元の単位の各点での成分。 -/
lemma unitCommaSectionTargetFiberArrow_hom {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaTargetFiberArrow G x (F.app (Opposite.op ⦋0⦌) x)
        (unitCommaSectionTargetFiberVertex η x)).toTruncated = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent η x := by
  rw [unitCommaSectionTargetFiberArrow_eq]
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy η) x).symm.trans
    (congrArg (fun α ↦ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α x) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom η))

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
