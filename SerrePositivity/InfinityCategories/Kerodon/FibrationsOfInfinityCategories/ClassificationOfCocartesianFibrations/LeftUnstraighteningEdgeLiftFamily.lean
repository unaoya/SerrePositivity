module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningMappingVertices

/-!
概要：既存の全写像空間の持ち上げを、指定辺で評価した実際の区間族を取り出す。
方針：元の普遍族を同じ辺の区間写像空間の頂点で制限する。
規約：選択を増やさず、leftUnstraighteningMappingSpaceMap の元の族を用いる。
使われ方：G8 の四角形①で、任意の始域への制限後に pointed 区間族を比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

variable {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
  (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G))

/-- 元の全写像空間の持ち上げを、同じ辺の頂点で制限する。 -/
def leftUnstraighteningEdgeLiftFamily :
    (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u} :=
  lift (𝟙 _) (SSet.const (show (leftUnstraighteningTransformationSpace F G) _⦋0⦌ from
    intervalMappingVertexOfEdge e)) ≫
    leftUnstraighteningTransformationFamilyLift F G

/-- 元の全写像空間の終点の族を、同じ辺の頂点で制限する。 -/
def leftUnstraighteningEdgeLiftMap : leftUnstraightening F ⟶ leftUnstraightening G :=
  lift (𝟙 _) (SSet.const (show (leftUnstraighteningTransformationSpace F G) _⦋0⦌ from
    intervalMappingVertexOfEdge e)) ≫ leftUnstraighteningMappingFamily F G

/-- 制限した終点は元の底への射影を保つ。 -/
lemma leftUnstraighteningEdgeLiftMap_projection :
    leftUnstraighteningEdgeLiftMap F G e ≫ leftUnstraighteningProjection G =
      leftUnstraighteningProjection F := by
  have hp : leftUnstraighteningMappingFamily F G ≫ leftUnstraighteningProjection G =
      fst _ _ ≫ leftUnstraighteningProjection F := pullback.lift_snd _ _ _
  rw [leftUnstraighteningEdgeLiftMap, Category.assoc, hp, ← Category.assoc,
    lift_fst, Category.id_comp]

/-- 制限した区間族の始点は、元の unstraightening の pointed 成分である。 -/
lemma leftUnstraighteningEdgeLiftFamily_zero :
    prismEndpoint 0 _ ≫ leftUnstraighteningEdgeLiftFamily F G e =
      pullback.fst pointedSpaceProjection F := by
  change simplexPrismVertex 1 0 _ ≫ leftUnstraighteningEdgeLiftFamily F G e = _
  rw [leftUnstraighteningEdgeLiftFamily, ← Category.assoc, ← parameterVertex_naturality,
    Category.assoc, leftUnstraighteningTransformationFamilyLift_start,
    ← Category.assoc, lift_fst, Category.id_comp]

/-- 制限した区間族は、元の辺の全 prism を被覆する。 -/
lemma leftUnstraighteningEdgeLiftFamily_projection :
    leftUnstraighteningEdgeLiftFamily F G e ≫ pointedSpaceProjection =
      (Δ[1] ◁ leftUnstraighteningProjection F) ≫ functorEdgePrism e := by
  rw [leftUnstraighteningEdgeLiftFamily, Category.assoc,
    leftUnstraighteningTransformationFamilyLift_projection,
    ← Category.assoc, parameterVertex_naturality, Category.assoc,
    leftUnstraighteningTransformationFamily_at_edge]

/-- 制限した区間族の終点は、同じ全写像空間の終点写像の pointed 成分である。 -/
lemma leftUnstraighteningEdgeLiftFamily_one :
    prismEndpoint 1 _ ≫ leftUnstraighteningEdgeLiftFamily F G e =
      leftUnstraighteningEdgeLiftMap F G e ≫ pullback.fst pointedSpaceProjection G := by
  have hp : leftUnstraighteningMappingFamily F G ≫ pullback.fst pointedSpaceProjection G =
      (simplexPrismVertex 1 1 (leftUnstraightening F) ▷
        leftUnstraighteningTransformationSpace F G) ≫
          leftUnstraighteningTransformationFamilyLift F G := pullback.lift_fst _ _ _
  change simplexPrismVertex 1 1 _ ≫ leftUnstraighteningEdgeLiftFamily F G e = _
  rw [leftUnstraighteningEdgeLiftFamily, leftUnstraighteningEdgeLiftMap,
    ← Category.assoc, ← parameterVertex_naturality, Category.assoc, Category.assoc, hp]

/-- 元の写像空間の比較の辺での値は、取り出した終点写像の相対頂点である。 -/
lemma leftUnstraighteningEdgeLiftMap_vertex :
    (leftUnstraighteningMappingSpaceMap F G).app _ (intervalMappingVertexOfEdge e) =
      relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
        (leftUnstraighteningEdgeLiftMap F G e) (leftUnstraighteningEdgeLiftMap_projection F G e) :=
  leftUnstraighteningMappingSpaceMap_vertex F G _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
