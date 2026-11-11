module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryPointedFunctor
public import SerrePositivity.KST.SConstruction.ExInfinityPointedEnrichedFunctor

/-! # 元の境界商から点つき Kan 値への全 native 関手
概要：同じ元の境界商の全族を、Ex∞ の点つき Kan 値へ厳密豊穣に送る。
方針：標準点つき豊穣関手と全 Hom を保持する Ex∞ 置換を合成して γ1 に渡す。
規約：BF の列は後続。使われ方：厳密 dg 入力に関する K の各実現段の ∞ 関手。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 同じ元の境界商の、全 native 入力族を保持する点つき Kan 値厳密豊穣関手。 -/
def presentedPerfectDGBoundaryKanEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedKanObject.{max (u + 1) v} :=
  (presentedPerfectDGBoundaryPointedEnrichedFunctor A r).comp SSet
    exInfinityPointedKanEnrichedFunctor

/-- Kan 実値の基点は、同じ元の境界商の基点の Ex∞ 単位への像。 -/
lemma presentedPerfectDGBoundaryKanEnrichedFunctor_obj (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGBoundaryKanEnrichedFunctor A r).obj C).obj =
      Under.mk ((boundaryReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).hom ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (boundaryReducedRealization r
            (stableCategoryModel (presentedPerfectDGStableCategory A C))).right) := rfl

/-- 同じ元の通常 dg 射による基点固定の境界商射。 -/
def presentedPerfectDGBoundaryPointedMap (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    (presentedPerfectDGBoundaryPointedEnrichedFunctor A r).obj C ⟶
      (presentedPerfectDGBoundaryPointedEnrichedFunctor A r).obj D :=
  boundaryReducedRealizationMap r
    (show stableCategoryModel (presentedPerfectDGStableCategory A C) ⟶
      stableCategoryModel (presentedPerfectDGStableCategory A D) from
        ⟨(presentedPerfectDGExactMap A F).hom,
          preservesCofiberData_of_isExactFunctor (presentedPerfectDGExactMap A F).hom⟩)

/-- 元の同じ境界商射に同じ Ex∞ 関手を適用した実際の Kan 射。 -/
def presentedPerfectDGBoundaryKanMap (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    (presentedPerfectDGBoundaryKanEnrichedFunctor A r).obj C ⟶
      (presentedPerfectDGBoundaryKanEnrichedFunctor A r).obj D :=
  exInfinityPointedKanMap (presentedPerfectDGBoundaryPointedMap A r F)

/-- 通常 dg 入力射では、同じ元の境界商射の Ex∞ 像を全 native Hom から回収する。 -/
lemma presentedPerfectDGBoundaryKanEnrichedFunctor_hom (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫
      (presentedPerfectDGBoundaryKanEnrichedFunctor A r).map C D =
        eHomEquiv SSet.{max (u + 1) v} (presentedPerfectDGBoundaryKanMap A r F) := by
  change eHomEquiv SSet.{max (u + 1) v} F ≫
    ((presentedPerfectDGBoundaryPointedEnrichedFunctor A r).map C D ≫
      exInfinityPointedKanEnrichedFunctor.map _ _) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ exInfinityPointedKanEnrichedFunctor.map _ _)
      (presentedPerfectDGBoundaryPointedEnrichedFunctor_hom A r F)).trans
        (exInfinityPointedKanEnrichedFunctor_hom (presentedPerfectDGBoundaryPointedMap A r F)))

/-- 元の同じ境界商から Kan 値への、元の基点を保つ Ex∞ 単位。 -/
def presentedPerfectDGBoundaryKanUnit (r : ℕ) (C : PerfDGInput.{u, v} A) :
    boundaryReducedRealization r (stableCategoryModel (presentedPerfectDGStableCategory A C)) ⟶
      ((presentedPerfectDGBoundaryKanEnrichedFunctor A r).obj C).obj :=
  exInfinityPointedUnit ((presentedPerfectDGBoundaryPointedEnrichedFunctor A r).obj C)

/-- 元の境界商から Kan 値への同じ単位の基礎射は anodyne。 -/
lemma presentedPerfectDGBoundaryKanUnit_anodyne (r : ℕ) (C : PerfDGInput.{u, v} A) :
    anodyneExtensions (presentedPerfectDGBoundaryKanUnit A r C).right :=
  exInfinityPointedUnit_anodyne ((presentedPerfectDGBoundaryPointedEnrichedFunctor A r).obj C)

/-- γ1 による、全 native dg 入力から点つき Kan 空間への各実現段の ∞ 関手。 -/
def presentedPerfectDGBoundaryKanInfinityFunctor (r : ℕ) :
    perfDGInputInfinity.{u, v} A ⟶ PointedKanInfinity.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (presentedPerfectDGBoundaryKanEnrichedFunctor A r)

/-- ∞ 関手の各頂点は、同じ元の境界商の基点を保持した Ex∞ Kan 値。 -/
lemma presentedPerfectDGBoundaryKanInfinityFunctor_vertex (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBoundaryKanInfinityFunctor A r).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex C) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((presentedPerfectDGBoundaryKanEnrichedFunctor A r).obj C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex _ C

end SerrePositivity.KST.SConstruction
