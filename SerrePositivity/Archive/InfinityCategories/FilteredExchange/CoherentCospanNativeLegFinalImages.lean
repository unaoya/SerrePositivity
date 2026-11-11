module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoChainTransport

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeTargetEvaluationComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeFiberSectionsIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeFinalFiberIso

/-!
概要：native な二脚の指定同型の共通点像を、既存の最終 fiber の指定同型へ同定する。
方針：明示した端点補正を保持し、同じ面比較の後合成を結合する。
規約：元の全三角形の指定値を保持。使われ方：模型比較の二脚の底の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "g" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d)
local notation "E" => coherentCospanNativeCommonPointFiberIso F X Y Z C b

/-- 左の指定二脚同型の共通点像は、同じ元の全三角形の最終 fiber 同型。 -/
lemma coherentCospanNativeLeftLegFinalImage_heq :
    HEq (((coherentCospanNativeLeftFiberSectionsIso F X Y Z C b).postcomp f).postcomp (E).hom)
      (coherentCospanNativeLeftFinalFiberIso F X Y Z C b) := by
  have h₀ : HEq
      (((coherentCospanNativeLeftFiberSectionsIso F X Y Z C b).postcomp f).postcomp (E).hom)
      ((coherentCospanNativeLeftDiagramSectionsIso F X Y Z C b).postcomp (f ≫ (E).hom)) := by
    unfold coherentCospanNativeLeftFiberSectionsIso
    exact functorIsoOfEq_postcomp_postcomp_heq _ _ _ _ _
  have h₁ : HEq
      ((coherentCospanNativeLeftDiagramSectionsIso F X Y Z C b).postcomp (f ≫ (E).hom))
      ((coherentCospanNativeLeftFaceSectionsIso F X Y Z C b 0).postcomp
        (coherentCospanNativeLeftTargetFiberEvaluation F X Y Z C b)) := by
    unfold coherentCospanNativeLeftDiagramSectionsIso
    refine (functorIsoOfEq_postcomp_heq _ _ _ _).trans ?_
    rw [functorIso_postcomp_postcomp]
    exact functorIso_postcomp_heq_of_map_eq _
      (coherentCospanNativeLeftTargetEvaluation_comparison F X Y Z C b).symm
  have h₂ := functorIsoOfEq_heq
    ((coherentCospanNativeLeftFaceSectionsIso F X Y Z C b 0).postcomp
      (coherentCospanNativeLeftTargetFiberEvaluation F X Y Z C b)) rfl
    (coherentTriangleTargetFiberEvaluation_eq F X Z C.toLeft C.fromLeft C.leftTriangle b _
      (coherentCospanNativeLeftTriangleDiagram_eq F X Y Z C b)
      (coherentCospanPointedFiberTriangle_left_projection F b X Y Z C))
  exact h₀.trans (h₁.trans h₂.symm)

/-- 右の指定同型にも同じ共通点像と同じ最終 fiber を使う。 -/
lemma coherentCospanNativeRightLegFinalImage_heq :
    HEq (((coherentCospanNativeRightFiberSectionsIso F X Y Z C b).postcomp g).postcomp (E).hom)
      (coherentCospanNativeRightFinalFiberIso F X Y Z C b) := by
  have h₀ : HEq
      (((coherentCospanNativeRightFiberSectionsIso F X Y Z C b).postcomp g).postcomp (E).hom)
      ((coherentCospanNativeRightDiagramSectionsIso F X Y Z C b).postcomp (g ≫ (E).hom)) := by
    unfold coherentCospanNativeRightFiberSectionsIso
    exact functorIsoOfEq_postcomp_postcomp_heq _ _ _ _ _
  have h₁ : HEq
      ((coherentCospanNativeRightDiagramSectionsIso F X Y Z C b).postcomp (g ≫ (E).hom))
      ((coherentCospanNativeRightFaceSectionsIso F X Y Z C b 0).postcomp
        (coherentCospanNativeRightTargetFiberEvaluation F X Y Z C b)) := by
    unfold coherentCospanNativeRightDiagramSectionsIso
    refine (functorIsoOfEq_postcomp_heq _ _ _ _).trans ?_
    rw [functorIso_postcomp_postcomp]
    exact functorIso_postcomp_heq_of_map_eq _
      (coherentCospanNativeRightTargetEvaluation_comparison F X Y Z C b).symm
  have h₂ := functorIsoOfEq_heq
    ((coherentCospanNativeRightFaceSectionsIso F X Y Z C b 0).postcomp
      (coherentCospanNativeRightTargetFiberEvaluation F X Y Z C b)) rfl
    (coherentTriangleTargetFiberEvaluation_eq F Y Z C.toRight C.fromRight C.rightTriangle b _
      (coherentCospanNativeRightTriangleDiagram_eq F X Y Z C b)
      (coherentCospanPointedFiberTriangle_right_projection F b X Y Z C))
  exact h₀.trans (h₁.trans h₂.symm)

end SerrePositivity.InfinityCategories.F2
