module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsUnstraighteningPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentableUnstraighteningEvaluationPost
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallTransformationEdgeFiberValue
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaPresheafEvaluation

/-!
概要：元の Yoneda 評価と標的の指定辺による後合成の全族での可換性。
方針：元の相対表示、恒等錐での評価、同じfiberの値比較の自然性を合成する。
規約：元の評価射を別の同値へ置き換えず、自然性を追加入力にしない。
使われ方：G14 の小さい生成族による射の可逆性の検出。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 元の Yoneda 評価は標的の元の辺の後合成と、同じ点での空間値の作用に全自然。 -/
def yonedaPresheafEvaluation_postcomposeIso {C : SSet.{u}} [Quasicategory C]
    (y : C _⦋0⦌)
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (functorVertex F) (functorVertex G)) :
    FunctorIso
      (postcompose (functorVertex (representablePresheafInfinity y))
          (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) ≫ yonedaPresheafEvaluation y G)
      (yonedaPresheafEvaluation y F ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (spaceInfinityEdgeValue (functorEdgeAt e (ULift.up (SSet.opObjEquiv.symm y))))) := by
  let Y := representablePresheafInfinity y
  let f := leftUnstraighteningEdgeLiftMap F G e
  let hf := leftUnstraighteningEdgeLiftMap_projection F G e
  let sf := smallLeftUnstraighteningOverMap F G f
  let sh := smallLeftUnstraighteningOverMap_projection F G f hf
  let sp := relativeFunctorPost (smallLeftUnstraighteningProjection F)
    (smallLeftUnstraighteningProjection G) sf sh (smallLeftUnstraighteningProjection Y)
  let bp := relativeFunctorPost (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection G) f hf (leftUnstraighteningProjection Y)
  let iF := smallLeftUnstraighteningRelativeFunctorIso Y F
  let iG := smallLeftUnstraighteningRelativeFunctorIso Y G
  have hs : (SSet.uliftFunctor.{u + 1, u}).map sp ≫ iG.hom = iF.hom ≫ bp :=
    smallLeftUnstraighteningRelativeFunctorIso_post Y F G f hf
  have hi := congrArg (fun k => iF.inv ≫ k ≫ iG.inv) hs
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] at hi
  have he := representableUnstraighteningEvaluation_post
    (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G) sf sh y
  have h₀ := (unstraighteningPinchedEdgeLiftPostcompositionIso Y F G e).postcomp
    (iG.inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (representableUnstraighteningEvaluation (smallLeftUnstraighteningProjection G) y) ≫
        (smallLeftUnstraighteningLiftedFiberValueEquivalence G (SSet.opObjEquiv.symm y)).hom)
  have h₁ := (smallTransformationEdge_fiberValueIso F G e (SSet.opObjEquiv.symm y)).precomp
    (leftUnstraighteningPinchedMappingSpaceMap Y F ≫ iF.inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (representableUnstraighteningEvaluation (smallLeftUnstraighteningProjection F) y))
  have hx : leftUnstraighteningPinchedMappingSpaceMap Y F ≫ bp ≫ iG.inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (representableUnstraighteningEvaluation (smallLeftUnstraighteningProjection G) y) =
      leftUnstraighteningPinchedMappingSpaceMap Y F ≫ iF.inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (representableUnstraighteningEvaluation (smallLeftUnstraighteningProjection F) y) ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (vertexFiberMap (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G)
            sf sh (SSet.opObjEquiv.symm y)) := by
    rw [← Category.assoc bp, ← hi]
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp, he, CategoryTheory.Functor.map_comp]
  dsimp only [bp, f, hf] at hx
  simp only [← Category.assoc] at hx h₀ h₁
  rw [hx] at h₀
  simpa only [yonedaPresheafEvaluation, Y, iF, iG, f, hf, sf, sh, bp,
    Category.assoc] using h₀ ≪≫ h₁

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
