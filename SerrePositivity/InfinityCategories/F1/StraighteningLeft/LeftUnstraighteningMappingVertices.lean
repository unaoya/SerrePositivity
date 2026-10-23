module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertices
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFamilyVertices
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingSpaceMap
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningComposition
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFunctorEdge

/-!
概要：写像空間全体の unstraightening 比較射を、一本の coherent な変換で評価する。
方針：辺を区間模型の頂点として表示し、普遍的な持ち上げをその頂点で制限する。
規約：個別の変換で選択した射との比較は、底を固定した写像空間内の同型で表す。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の比較射と変換への既存の作用の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：区間模型の普遍的な族を実際の辺の頂点で制限すると、その辺の Yoneda 射を回収する。
方針：内部 Hom の族の頂点評価と通常の射の関手頂点の往復を使う。
規約：標的 X の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6、変換の空間の普遍族から一本の変換を取り出す。 -/
lemma intervalMappingUniversal_at_edge {X : SSet.{u}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (intervalMappingVertexOfEdge e)) ≫
      intervalMappingUncurry (𝟙 (intervalMappingSpace x y)) = SSet.yonedaEquiv.symm e.edge := by
  change lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (intervalMappingVertexOfEdge e)) ≫
    uncurry (vertexFiberι ((pre (boundary 1).ι).app X)
      (functorVertex (intervalMappingBoundary x y))) = _
  exact (uncurry_at_vertex _ (intervalMappingVertexOfEdge e)).trans
    ((functorVertexEquiv (Δ[1] : SSet.{u}) X).symm_apply_apply _)

/-- 概要：変換の普遍的な評価を辺の頂点で制限すると、その変換の prism 表示になる。
方針：追加パラメーターの頂点への制限と区間模型の普遍族の計算を使う。
規約：底 B は任意。
使われ方：Kerodon Corollary 5.6.0.6、普遍的な評価と一本の変換の一致。 -/
lemma leftUnstraighteningTransformationFamily_at_edge {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G)) :
    lift (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ B)) (SSet.const (intervalMappingVertexOfEdge e)) ≫
      leftUnstraighteningTransformationFamily F G = functorEdgePrism e := by
  rw [leftUnstraighteningTransformationFamily, functorParameterizedPrism_at_parameter]
  exact congrArg functorFamilyPrism (intervalMappingUniversal_at_edge e)

/-- 概要：写像空間の比較射の頂点での値は、その頂点で制限した底上の族の相対関手頂点。
方針：比較射の相対 curry の頂点での計算を適用する。
規約：x は変換の空間の任意の頂点。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の比較射が表す具体的な底上の射。 -/
lemma leftUnstraighteningMappingSpaceMap_vertex {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) :
    (leftUnstraighteningMappingSpaceMap F G).app _ x =
      relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
        (lift (𝟙 (leftUnstraightening F)) (SSet.const x) ≫ leftUnstraighteningMappingFamily F G) (by
          have hp : leftUnstraighteningMappingFamily F G ≫ leftUnstraighteningProjection G =
              fst (leftUnstraightening F) (leftUnstraighteningTransformationSpace F G) ≫
                leftUnstraighteningProjection F := pullback.lift_snd _ _ _
          rw [Category.assoc, hp, ← Category.assoc, lift_fst, Category.id_comp]) :=
  relativeFunctorCurry_vertex _ _ _ _ x

/-- 概要：写像空間全体の比較射を辺で評価した値は、その辺に個別に選択した unstraightening の射と相対写像空間内で同型。
方針：普遍的な持ち上げを辺の頂点で制限し、持ち上げの可縮な選択空間で比較する。
規約：同型は底を固定した写像空間内に置く。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の比較射と変換への作用の整合性。 -/
noncomputable def leftUnstraighteningMappingSpaceMap_edgeVertexIso {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F) (functorVertex G)) :
    VertexIso (relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
      (leftUnstraighteningEdgeMap F G e).val (leftUnstraighteningEdgeMap F G e).property)
      ((leftUnstraighteningMappingSpaceMap F G).app _ (intervalMappingVertexOfEdge e)) := by
  let x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌ := intervalMappingVertexOfEdge e
  let W := lift (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F)) (SSet.const x) ≫
    leftUnstraighteningTransformationFamilyLift F G
  let g := lift (𝟙 (leftUnstraightening F)) (SSet.const x) ≫ leftUnstraighteningMappingFamily F G
  have hg : g ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F := by
    have hp : leftUnstraighteningMappingFamily F G ≫ leftUnstraighteningProjection G =
        fst (leftUnstraightening F) (leftUnstraighteningTransformationSpace F G) ≫
          leftUnstraighteningProjection F := pullback.lift_snd _ _ _
    rw [Category.assoc, hp, ← Category.assoc, lift_fst, Category.id_comp]
  have hW₀ : prismEndpoint 0 _ ≫ W = pullback.fst pointedSpaceProjection F := by
    change simplexPrismVertex 1 0 (leftUnstraightening F) ≫ W = _
    dsimp only [W]
    rw [← Category.assoc, ← parameterVertex_naturality, Category.assoc,
      leftUnstraighteningTransformationFamilyLift_start, ← Category.assoc, lift_fst, Category.id_comp]
  have hWp : W ≫ pointedSpaceProjection =
      (Δ[1] ◁ leftUnstraighteningProjection F) ≫ functorEdgePrism e := by
    dsimp only [W]
    rw [Category.assoc, leftUnstraighteningTransformationFamilyLift_projection,
      ← Category.assoc, parameterVertex_naturality, Category.assoc,
      leftUnstraighteningTransformationFamily_at_edge]
  have hW₁ : prismEndpoint 1 _ ≫ W = g ≫ pullback.fst pointedSpaceProjection G := by
    have hp : leftUnstraighteningMappingFamily F G ≫ pullback.fst pointedSpaceProjection G =
        (simplexPrismVertex 1 1 (leftUnstraightening F) ▷
          leftUnstraighteningTransformationSpace F G) ≫ leftUnstraighteningTransformationFamilyLift F G :=
      pullback.lift_fst _ _ _
    change simplexPrismVertex 1 1 (leftUnstraightening F) ≫ W = _
    dsimp only [W, g]
    rw [← Category.assoc, ← parameterVertex_naturality, Category.assoc, Category.assoc, hp]
  let h := leftUnstraighteningTransformationMap_witnessIso F G (functorEdgePrism e)
    (functorEdgePrism_zero e) (functorEdgePrism_one e) W hW₀ hWp g hg hW₁
  exact h ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk
    (leftUnstraighteningMappingSpaceMap_vertex F G x).symm)

end SerrePositivity.InfinityCategories
