module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SmallPointedFiberNaturality
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningMappingFiberTransport
public import SerrePositivity.InfinityCategories.F1.InvertibleLeftTransport
public import SerrePositivity.InfinityCategories.F1.LeftFibrationFiberComparison

/-!
概要：可逆な coherent 変換の指定された小さい全空間作用は前合成同値。
方針：各 fiber で普遍輸送と照合し、縮小同型で同値性を反映して fiber 判定を使う。
規約：底の quasicategory 性を仮定せず、元の選択済みの全空間射を保持する。
使われ方：P_Σ の評価全錐と積全錐の同型を、元の余極限 Kan 模型へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (t : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (ht : IsInvertibleEdge (intervalMappingEdgeOfVertex t))
include ht

/-- 元の指定変換の普遍 pointed fiber 作用は、可逆な評価辺の輸送との比較により同値。 -/
lemma coherentInvertiblePointedFiberMap_isQCatEquivalence (b : B _⦋0⦌) :
    IsQCatEquivalence (leftUnstraighteningPointedFiberMap F G
      (leftUnstraighteningMappingVertexMap F G t).val
      (leftUnstraighteningMappingVertexMap F G t).property (ULift.up b)) := by
  have he : IsInvertibleEdge (functorEdgeAt (intervalMappingEdgeOfVertex t) (ULift.up b)) :=
    (isInvertibleEdge_congr (e :=
      (functorEdgeAt (intervalMappingEdgeOfVertex t) (ULift.up b)).toTruncated)
      (f := ((intervalMappingEdgeOfVertex t).map
        (evaluateFunctorAt (ULift.up b))).toTruncated) rfl).mpr
          (ht.map (evaluateFunctorAt (ULift.up b)))
  have h := edgeTransport_isQCatEquivalence_of_isInvertibleEdge pointedSpaceProjection _ he
  exact h.ofFunctorIso
    (leftUnstraighteningMappingVertex_pointedFiberTransportIso F G t (ULift.up b)).symm

/-- 元の小さい全空間作用の各 fiber は、元の宇宙でも同値。 -/
lemma coherentInvertibleTotalMap_fiber_isQCatEquivalence (b : B _⦋0⦌) :
    IsQCatEquivalence (vertexFiberMap
      (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G)
      (F2.coherentTransformationTotalMap F G t)
      (F2.coherentTransformationTotalMap_projection F G t) b) := by
  have h := (qCatEquivalenceOfIso (smallPointedFiberIso F b)).isQCatEquivalence.comp
    (coherentInvertiblePointedFiberMap_isQCatEquivalence F G t ht b)
  change IsQCatEquivalence ((smallPointedFiberIso F b).hom ≫ _) at h
  rw [← smallPointedFiberIso_naturality F G t b] at h
  exact (isQCatEquivalence_ulift_iff_of_kan _).mp
    ((qCatEquivalenceOfIso (smallPointedFiberIso G b)).isQCatEquivalence.cancel_right h)

/-- 任意の小さい底上で、元の可逆変換の選択済み全空間射は前合成同値。 -/
lemma coherentInvertibleTotalMap_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (F2.coherentTransformationTotalMap F G t) :=
  isPrecompositionEquivalence_of_leftFibration_fibers _ _ _
    (F2.coherentTransformationTotalMap_projection F G t)
    (coherentInvertibleTotalMap_fiber_isQCatEquivalence F G t ht)

end SerrePositivity.InfinityCategories.HomotopyLimits
