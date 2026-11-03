module

public import SerrePositivity.InfinityCategories.Coherent.Quasicategory
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Coherent.Edges
public import SerrePositivity.InfinityCategories.F1.Coherent.HomEquivalence
public import SerrePositivity.InfinityCategories.F1.Coherent.HomNaturality
public import SerrePositivity.InfinityCategories.F1.Coherent.HomOrdinary
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1B.KanComplex.HomotopyClasses
public import SerrePositivity.InfinityCategories.F1.CatInfinity.CatFunctorCoreIso
public import SerrePositivity.InfinityCategories.PinchedHom.Basic

/-!
概要：𝒮 の平行な辺の類の一致から、元の Kan 射のホモトピーを回収する。
方針：coherent Hom 比較の連結成分上の単射性と Kan 関手空間の成分判定を使う。
規約：同じ二対象間の指定された関手を比較する。
使われ方：native な空間の錐の脚と元の射影の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：𝒮 のホモトピー圏で同じ射を表す Kan 射は実際のホモトピーで結ばれる。
方針：写像空間の連結成分の単射性を通して元の内部 Hom の成分を一致させる。
規約：元の射 f と g を保持する。
使われ方：錐の自然性を元の Kan 射のホモトピーへ戻す。 -/
lemma spaceInfinity_homotopy_of_homMk_eq {X Y : KanObject.{u}} {f g : X ⟶ Y}
    (h : SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge g).toTruncated) :
    Nonempty (SSet.Homotopy f g) := by
  let a := ULift.up.{u + 1} (SimplicialCategory.homEquiv' X Y f)
  let b := ULift.up.{u + 1} (SimplicialCategory.homEquiv' X Y g)
  have hf : pinchedHomVertexEquiv _ _
      ((coherentHomComparison X Y).app _ a) = (coherentNerveEdge f).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact coherentHomComparison_ordinary f
  have hg : pinchedHomVertexEquiv _ _
      ((coherentHomComparison X Y).app _ b) = (coherentNerveEdge g).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact coherentHomComparison_ordinary g
  have hp : SSet.mapπ₀ (coherentHomComparison X Y) (SSet.π₀.mk a) =
      SSet.mapπ₀ (coherentHomComparison X Y) (SSet.π₀.mk b) := by
    apply pinchedHomPiZeroToHom_injective (coherentNerveVertex X) (coherentNerveVertex Y)
    change SSet.Truncated.HomotopyCategory.homMk
      (pinchedHomVertexEquiv _ _ ((coherentHomComparison X Y).app _ a)) =
      SSet.Truncated.HomotopyCategory.homMk
        (pinchedHomVertexEquiv _ _ ((coherentHomComparison X Y).app _ b))
    rwa [hf, hg]
  have hp :=
    (coherentHomComparison_isSimplicialHomotopyEquivalence X Y).mapPiZero_bijective.injective hp
  have hq := congrArg (coherentUliftPiZeroDown (SimplicialCategory.sHom X Y)) hp
  change SSet.π₀.mk (SimplicialCategory.homEquiv' X Y f) =
    SSet.π₀.mk (SimplicialCategory.homEquiv' X Y g) at hq
  change SSet.π₀.mk (functorVertex f) = SSet.π₀.mk (functorVertex g) at hq
  exact (functorVertex_piZero_eq_iff_homotopy f g).mp hq

end SerrePositivity.InfinityCategories.F2
