module
public import SerrePositivity.InfinityCategories.Stable.KanModels.KanForgetDetection
public import SerrePositivity.KST.Fibration.KanClosedEvaluation
public import SerrePositivity.KST.SConstruction.PointedKanEnrichedEquivalences
public import SerrePositivity.InfinityCategories.F1.Transport.InvertibleLeftTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanWhiteheadComparison
public import SerrePositivity.InfinityCategories.F1.Coherent.NerveHomEdgeNaturality

/-! # 基点を忘れた同じ coherent 辺の可逆性は、元の点つき辺へ反映される -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 基点忘却の全 Hom 作用は、同じ元の基礎射の coherent な辺を回収する。 -/
theorem pointedKanForget_edge {X Y : PointedKanObject.{u}} (f : X ⟶ Y) :
    (coherentNerveMap pointedKanForgetEnriched).app (Opposite.op ⦋1⦌)
      (coherentNerveEdge f).edge =
      (coherentNerveEdge (show pointedKanForgetEnriched.obj X ⟶
        pointedKanForgetEnriched.obj Y from f.hom.right)).edge :=
  coherentNerveMap_edge_of_homEquiv _ _ _ (pointedClosedHomInclusion_hom f.hom)

/-- 基点忘却後に同じ辺が可逆なら、元の点つき Kan 射の同じ辺も可逆。 -/
theorem pointedKan_isInvertible_of_forget {X Y : PointedKanObject.{u}} (f : X ⟶ Y)
    (hf : IsInvertibleEdge (X := SpaceInfinity.{u}) ((coherentNerveEdge f).toTruncated.map
      ((truncation 2).map (coherentNerveMap pointedKanForgetEnriched)))) :
    IsInvertibleEdge (coherentNerveEdge f) := by
  have he : IsInvertibleEdge (X := SpaceInfinity.{u})
      (coherentNerveEdge (show pointedKanForgetEnriched.obj X ⟶
        pointedKanForgetEnriched.obj Y from f.hom.right)) :=
    (isInvertibleEdge_congr (X := SpaceInfinity.{u})
      (e := (coherentNerveEdge f).toTruncated.map
        ((truncation 2).map (coherentNerveMap pointedKanForgetEnriched)))
      (pointedKanForget_edge f)).mp hf
  exact pointedKanObject_edge_isInvertible_of_piIsomorphism f
    (_root_.SerrePositivity.InfinityCategories.Stable.KanModels.kanMap_piIsomorphism_of_invertible
      (X := pointedKanForgetEnriched.obj X) (Y := pointedKanForgetEnriched.obj Y) f.hom.right he)

end SerrePositivity.KST.Fibration
