module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryKanFunctor

/-! # 元の全境界商作用と Kan 置換単位の厳密な自然性
概要：点つき Ex∞ の全 Hom 作用を元の商作用で回収し、単位の全族自然性を証明する。
方針：basedHom の包含と元の閉 Hom 作用の比較を合成し、単位の評価式を使う。
規約：通常の射に制限しない。使われ方：同じ元の K 模型と全入力族の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- Kan 全 Hom 作用の包含後には、元の同じ商の全作用を Ex∞ で写して回収する。 -/
lemma presentedPerfectDGBoundaryKanEnrichedFunctor_inclusion (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBoundaryKanEnrichedFunctor A r).map C D ≫
      PointedObject.basedHomι
        (((presentedPerfectDGBoundaryKanEnrichedFunctor A r).obj C).obj)
        (((presentedPerfectDGBoundaryKanEnrichedFunctor A r).obj D).obj) =
      (presentedPerfectDGBoundaryReducedEnrichedFunctor A r).map C D ≫
        coaugmentedClosedFamilyMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
          ((presentedPerfectDGBoundaryReducedEnrichedFunctor A r).obj C).obj
          ((presentedPerfectDGBoundaryReducedEnrichedFunctor A r).obj D).obj := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => (presentedPerfectDGBoundaryPointedEnrichedFunctor A r).map C D ≫ q)
      (exInfinityPointedKanEnrichedFunctor_inclusion
        ((presentedPerfectDGBoundaryPointedEnrichedFunctor A r).obj C)
        ((presentedPerfectDGBoundaryPointedEnrichedFunctor A r).obj D))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun q => q ≫ coaugmentedClosedFamilyMap
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
            ((presentedPerfectDGBoundaryReducedEnrichedFunctor A r).obj C).obj
            ((presentedPerfectDGBoundaryReducedEnrichedFunctor A r).obj D).obj)
          (presentedPerfectDGBoundaryReducedEnrichedFunctor_family A r C D))))

/-- 元の商から Kan 値への同じ単位は、全 native dg 入力族の作用と厳密に可換。 -/
lemma presentedPerfectDGBoundaryKanUnit_action (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGBoundaryKanUnit A r C).right ▷
      (C ⟶[SSet.{max (u + 1) v}] D)) ≫
        uncurry ((presentedPerfectDGBoundaryKanEnrichedFunctor A r).map C D ≫
          PointedObject.basedHomι
            (((presentedPerfectDGBoundaryKanEnrichedFunctor A r).obj C).obj)
            (((presentedPerfectDGBoundaryKanEnrichedFunctor A r).obj D).obj)) =
      presentedPerfectDGBoundaryReducedAction A r C D ≫
        (presentedPerfectDGBoundaryKanUnit A r D).right := by
  have h := congrArg (uncurry (C := SSet.{max (u + 1) v}))
    (presentedPerfectDGBoundaryKanEnrichedFunctor_inclusion A r C D)
  exact (congrArg (fun q => ((presentedPerfectDGBoundaryKanUnit A r C).right ▷
    (C ⟶[SSet.{max (u + 1) v}] D)) ≫ q) h).trans
      ((coaugmentedClosedFamilyMap_action _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
        ((presentedPerfectDGBoundaryReducedEnrichedFunctor A r).map C D)).trans
          (congrArg (fun q => q ≫ (presentedPerfectDGBoundaryKanUnit A r D).right)
            (uncurry_curry (presentedPerfectDGBoundaryReducedAction A r C D))))

end SerrePositivity.KST.SConstruction
