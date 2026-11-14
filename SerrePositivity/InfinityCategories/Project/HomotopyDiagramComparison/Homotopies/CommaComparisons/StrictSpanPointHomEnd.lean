module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.SpanNerveHornIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpanCoconePointHomEnd
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.LiftedShapeNerveIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.VertexFiberMapIso

/-!
概要：通常の span の持ち上げた nerve の余錐空間を、二辺のホーン上の点 Hom の end へ移す。
方針：宇宙の二重の持ち上げを除いた厳密な同型で形状を合わせ、固定終点の制限同型を合成する。
規約：任意の quasicategory 値図式に適用する。使われ方：Kan 値 span の native な余極限余錐への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 通常の小さい span の持ち上げた nerve と、同じ宇宙の二辺のホーンの厳密な同型。 -/
def strictSpanHornIso :
    (SSet.uliftFunctor.{v, u}).obj (nerve (AsSmall.{u} WalkingSpan)) ≅
      (horn 2 0 : SSet.{max u v}) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedAsSmallNerveIso WalkingSpan ≪≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanNerveHornIso

/-- 任意の形状同型による余錐の制限は、固定終点の空間でも実際の同型。 -/
instance cosliceRestrictionFiberMap_isIso {K L X : SSet.{u}} (p : K ⟶ X)
    (i : L ⟶ K) [IsIso i] (y : X _⦋0⦌) : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p i y) := by
  change IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (i ≫ p))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection p i) y)
  infer_instance

variable {X : SSet.{max u v}} [Quasicategory X]
  (p : (SSet.uliftFunctor.{v, u}).obj (nerve (AsSmall.{u} WalkingSpan)) ⟶ X) (y : X _⦋0⦌)

/-- 持ち上げた通常の span の図式を、二辺のホーン上で厳密に表示する。 -/
def strictSpanHornDiagram : (horn 2 0 : SSet.{max u v}) ⟶ X := strictSpanHornIso.inv ≫ p

/-- 通常の span の余錐空間から、同型で表示した三頂点の点 Hom の end への比較。 -/
def strictSpanCoconeToPointHomEnd :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{max u v} WalkingCospan))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanPointHomCospan (strictSpanHornDiagram p) y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p strictSpanHornIso.inv y ≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanCoconeToPointHomEnd (strictSpanHornDiagram p) y

/-- 通常の span の余錐空間も、その三頂点の点 Hom の end と実際にホモトピー同値。 -/
lemma strictSpanCoconeToPointHomEnd_homotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (strictSpanCoconeToPointHomEnd p y) := by
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) y) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_kanComplex p y
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (strictSpanHornIso.inv ≫ p)) y) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace_kanComplex _ y
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p strictSpanHornIso.inv y)).comp
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spanCoconeToPointHomEnd_homotopyEquivalence (strictSpanHornDiagram p) y)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
