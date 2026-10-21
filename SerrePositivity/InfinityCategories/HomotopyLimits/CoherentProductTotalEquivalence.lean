module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentProductSmallFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiberProductVertexIso
public import SerrePositivity.InfinityCategories.F1.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.F1B.WeakHomotopy

/-!
概要：点ごとの coherent 積の小さい全空間から元の引き戻しへの指定比較は前合成同値。
方針：元の比較の各 fiber を二射影の対と厳密に同定し、left fibration の fiber 判定を使う。
規約：底の quasicategory 性を要求しない。使われ方：sifted 余極限と二項積の交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 同じ底上の二つの left fibration の引き戻しの射影も left fibration。 -/
lemma fiberProductVertexProjection_leftFibration {E D B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q] :
    LeftFibration (pullback.fst p q ≫ p) :=
  ⟨leftFibrations.comp_mem _ _
    (leftFibrations.pullback_fst p q (LeftFibration.mem (p := q))) (LeftFibration.mem (p := p))⟩

attribute [local instance] fiberProductVertexProjection_leftFibration
  vertexFiber_kanComplex_of_leftFibration kanTensor_isKan
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 元の小さい全空間の比較は元の底を厳密に保つ。 -/
lemma coherentSpaceTensorProductTotalComparison_projection :
    coherentSpaceTensorProductTotalComparison F G ≫
      (pullback.fst (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G) ≫
        smallLeftUnstraighteningProjection F) =
      smallLeftUnstraighteningProjection (coherentSpaceTensorProduct F G) := by
  rw [← Category.assoc, coherentSpaceTensorProductTotalComparison_fst]
  exact F2.coherentTransformationTotalMap_projection _ _ _

/-- 元の比較の fiber 射を積表示へ移すと、元の二つの小さい fiber 射の対そのもの。 -/
lemma coherentSpaceTensorProductTotalComparison_fiber (b : B _⦋0⦌) :
    vertexFiberMap
      (smallLeftUnstraighteningProjection (coherentSpaceTensorProduct F G))
      (pullback.fst (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G) ≫
        smallLeftUnstraighteningProjection F)
      (coherentSpaceTensorProductTotalComparison F G)
      (coherentSpaceTensorProductTotalComparison_projection F G) b ≫
        (fiberProductVertexIso (smallLeftUnstraighteningProjection F)
          (smallLeftUnstraighteningProjection G) b).hom = coherentProductSmallFiberMap F G b := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, fiberProductVertexIso_fst, vertexFiberMap_comp]
    simp only [coherentSpaceTensorProductTotalComparison_fst,
      coherentProductSmallFiberMap, lift_fst]
  · rw [Category.assoc, fiberProductVertexIso_snd, vertexFiberMap_comp]
    simp only [coherentSpaceTensorProductTotalComparison_snd,
      coherentProductSmallFiberMap, lift_snd]

/-- 元の比較射の各 fiber は同値。 -/
lemma coherentSpaceTensorProductTotalComparison_fiber_isQCatEquivalence (b : B _⦋0⦌) :
    IsQCatEquivalence (vertexFiberMap
      (smallLeftUnstraighteningProjection (coherentSpaceTensorProduct F G))
      (pullback.fst (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G) ≫
        smallLeftUnstraighteningProjection F)
      (coherentSpaceTensorProductTotalComparison F G)
      (coherentSpaceTensorProductTotalComparison_projection F G) b) := by
  apply (qCatEquivalenceOfIso (fiberProductVertexIso (smallLeftUnstraighteningProjection F)
    (smallLeftUnstraighteningProjection G) b)).isQCatEquivalence.cancel_right
  change IsQCatEquivalence (_ ≫ (fiberProductVertexIso (smallLeftUnstraighteningProjection F)
    (smallLeftUnstraighteningProjection G) b).hom)
  rw [coherentSpaceTensorProductTotalComparison_fiber]
  exact coherentProductSmallFiberMap_isQCatEquivalence F G b

/-- 任意の小さい底上で、元の全空間の引き戻しへの指定比較は前合成同値。 -/
lemma coherentSpaceTensorProductTotalComparison_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (coherentSpaceTensorProductTotalComparison F G) :=
  isPrecompositionEquivalence_of_leftFibration_fibers _ _ _
    (coherentSpaceTensorProductTotalComparison_projection F G)
    (coherentSpaceTensorProductTotalComparison_fiber_isQCatEquivalence F G)

/-- 同じ元の全空間比較は弱ホモトピー同値。 -/
lemma coherentSpaceTensorProductTotalComparison_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (coherentSpaceTensorProductTotalComparison F G) := by
  have h := coherentSpaceTensorProductTotalComparison_isPrecompositionEquivalence F G
  exact h.isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
