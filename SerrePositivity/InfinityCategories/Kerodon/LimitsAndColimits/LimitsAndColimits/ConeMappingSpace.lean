module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinSliceRestriction

/-!
概要：指定頂点から元の図式への錐空間と、任意の部分形状への制限を構成する。
方針：slice の頂点射影の fiber と、その射影を保つ制限射を使う。
規約：元の頂点と全単体を保持。使われ方：有限形状の接着による極限空間の比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 指定頂点を固定した元の図式上の錐空間。 -/
def coneMappingSpace {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) x

/-- quasicategory の元の図式の頂点固定の錐空間は Kan 複体。 -/
instance coneMappingSpace_kanComplex {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : KanComplex (coneMappingSpace p x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) x

/-- 部分形状への制限は元の錐の頂点を固定した fiber に誘導される。 -/
def coneRestrictionFiberMap {K L X : SSet.{u}} (p : K ⟶ X) (i : L ⟶ K)
    (x : X _⦋0⦌) : coneMappingSpace p x ⟶ coneMappingSpace (i ≫ p) x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p i) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanSliceOverRestrict_projection p i) x

/-- 頂点固定の制限は包含後に元の slice の制限となる。 -/
lemma coneMappingSpace_restrict_ι {K L X : SSet.{u}} (p : K ⟶ X) (i : L ⟶ K)
    (x : X _⦋0⦌) :
    coneRestrictionFiberMap p i x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (i ≫ p)) x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι _ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
