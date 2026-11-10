module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionKanFunctor
public import SerrePositivity.KST.SConstruction.ExInfinityPointedFamilies
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryFamilyEvaluation

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

/-- Kan 作用の包含は、同じ元の点つき全族の包含を経由する。 -/
lemma presentedPerfectDGOneDirectionKanEnrichedFunctor_family_inclusion (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    (presentedPerfectDGOneDirectionKanEnrichedFunctor A r).map C D ≫
      PointedObject.basedHomι
        (((presentedPerfectDGOneDirectionKanEnrichedFunctor A r).obj C).obj)
        (((presentedPerfectDGOneDirectionKanEnrichedFunctor A r).obj D).obj) =
    ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).map C D ≫
      PointedObject.basedHomι
        ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C).obj
        ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj D).obj) ≫
      coaugmentedClosedFamilyMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
        ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C).obj.right
        ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj D).obj.right :=
  exInfinityPointedFamily_inclusion
    ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C)
    ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj D)
    ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).map C D)

/-- 元の商から Kan 値への同じ単位は、全 native dg 入力族の作用と厳密に可換。 -/
lemma presentedPerfectDGOneDirectionKanUnit_action (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGOneDirectionKanUnit A r C).right ▷
      (C ⟶[SSet.{max (u + 1) v}] D)) ≫
        uncurry ((presentedPerfectDGOneDirectionKanEnrichedFunctor A r).map C D ≫
          PointedObject.basedHomι
            (((presentedPerfectDGOneDirectionKanEnrichedFunctor A r).obj C).obj)
            (((presentedPerfectDGOneDirectionKanEnrichedFunctor A r).obj D).obj)) =
      presentedPerfectDGOneDirectionReducedAction A r C D ≫
        (presentedPerfectDGOneDirectionKanUnit A r D).right := by
  have h := exInfinityPointedFamily_unit_action
    ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C)
    ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj D)
    ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).map C D)
  exact h.trans (congrArg (fun q => q ≫
    (presentedPerfectDGOneDirectionKanUnit A r D).right)
    (presentedPerfectDGOneDirectionReducedFamilyMap_evaluation A r C D))

end SerrePositivity.KST.SConstruction
