module
public import SerrePositivity.KST.Fibration.KanClosedEvaluation
public import SerrePositivity.KST.SConstruction.PointedKanEnrichedEquivalences
public import SerrePositivity.InfinityCategories.F1.InvertibleLeftTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanWhiteheadComparison
public import SerrePositivity.InfinityCategories.F1.CoherentNerveHomEdgeNaturality

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

/-- 元の Kan 射の coherent な可逆性は、同じ射の全基点 π 同値性を与える。 -/
theorem kanMap_piIsomorphism_of_invertible {X Y : KanObject.{u}} (f : X ⟶ Y)
    (hf : IsInvertibleEdge (coherentNerveEdge f)) : Spectra.KanPiIsomorphism f := by
  have ht := edgeTransport_isQCatEquivalence_of_isInvertibleEdge
    pointedSpaceProjection (coherentNerveEdge f) hf
  have he := (pointedSpaceTransport_coherentEdge_isQCatEquivalence_iff f).mp ht
  exact kanPiIsomorphism_of_homotopyEquivalence f he.isSimplicialHomotopyEquivalence

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
    (kanMap_piIsomorphism_of_invertible
      (X := pointedKanForgetEnriched.obj X) (Y := pointedKanForgetEnriched.obj Y) f.hom.right he)

end SerrePositivity.KST.Fibration
