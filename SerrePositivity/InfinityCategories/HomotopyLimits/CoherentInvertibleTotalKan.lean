module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentInvertibleTotalMap
public import SerrePositivity.InfinityCategories.HomotopyLimits.TotalKanNativeCoconeComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ContinuousKanWeakFunctoriality
public import SerrePositivity.InfinityCategories.F1B.WeakHomotopyInverse

/-!
概要：元の可逆変換の全空間作用を、元の余極限 Kan 模型の指定同値辺へ移す。
方針：前合成同値の弱同値性を Kan 置換へ移し、元の辺と全余錐作用を保持する。
規約：底の quasicategory 性は不要。単位と元の余極限余錐を変更しない。
使われ方：元の P_Σ 評価錐と反復積錐の比較の余極限への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (t : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)

/-- 元の指定全空間作用の、元の余極限 Kan 模型間の Kan 像。 -/
def coherentTransformationTotalKanMap : F2.coherentDiagramTotalKan F ⟶
    F2.coherentDiagramTotalKan G :=
  F2.continuousKanReplacement.map (F2.coherentTransformationTotalMap F G t)

/-- 同じ Kan 像は、元の両全空間の置換単位と厳密に可換。 -/
lemma coherentTransformationTotalKanMap_unit :
    F2.continuousKanReplacementUnit.app (smallLeftUnstraightening F) ≫
      coherentTransformationTotalKanMap F G t =
        F2.coherentTransformationTotalMap F G t ≫
          F2.continuousKanReplacementUnit.app (smallLeftUnstraightening G) :=
  (F2.continuousKanReplacementUnit.naturality _).symm

/-- 元の可逆変換の Kan 像には実際の単体的ホモトピー逆がある。 -/
lemma coherentInvertibleTotalKanMap_homotopyEquivalence
    (ht : IsInvertibleEdge (intervalMappingEdgeOfVertex t)) :
    IsSimplicialHomotopyEquivalence (coherentTransformationTotalKanMap F G t) :=
  (F2.continuousKanReplacement_map_isWeakHomotopyEquivalence _
    (coherentInvertibleTotalMap_isPrecompositionEquivalence F G t ht).isWeakHomotopyEquivalence
      ).isSimplicialHomotopyEquivalence

/-- 同じ Kan 像の元の coherent 辺は可逆である。 -/
lemma coherentInvertibleTotalKanNativeEdge_isInvertible
    (ht : IsInvertibleEdge (intervalMappingEdgeOfVertex t)) :
    IsInvertibleEdge (totalKanNativeEdge F G (coherentTransformationTotalKanMap F G t)) := by
  apply (isInvertibleEdge_congr (e :=
    (totalKanNativeEdge F G (coherentTransformationTotalKanMap F G t)).toTruncated)
    (f := (coherentNerveEdge (C := KanObject.{u})
      (X := F2.coherentDiagramTotalKanObject F) (Y := F2.coherentDiagramTotalKanObject G)
      (coherentTransformationTotalKanMap F G t)).toTruncated) rfl).mpr
  exact coherentKanEdge_isInvertible_of_isQCatEquivalence
    (coherentInvertibleTotalKanMap_homotopyEquivalence F G t ht).isQCatEquivalence

/-- 元の同じ可逆比較辺による全余錐作用は、元の指定 Kan 射の単位表現に一致する。 -/
def coherentTransformationTotalKanNativeCoconeIso :=
  totalKanNativeCoconeIso F G (coherentTransformationTotalKanMap F G t)

end SerrePositivity.InfinityCategories.HomotopyLimits
