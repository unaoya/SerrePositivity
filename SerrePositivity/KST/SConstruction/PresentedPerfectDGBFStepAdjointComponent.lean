module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFStepOmega

/-! # 実再帰 BF 構造随伴の元の組み立て成分
概要：同じ実円柱次段の構造随伴は、元の S₁ 比較と右脚の随伴を成分で結ぶ。
方針：元の円柱四角形を curry し、suspension と随伴の自然性を使う。
規約：Kan 模型の逆は選ばない。使われ方：旧 SOA 構造射との点つき比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet Spectra
open Spectra.PointedMapping SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ実次段の構造随伴は、元の左右脚の随伴四角形を成分で回収する。 -/
lemma presentedPerfectDGBFStepAdjoint_component (r : ℕ)
    (S : PresentedPerfectDGBFStage.{u, v} A r) (C : PerfDGInput.{u, v} A) :
    componentOf
        (((presentedPerfectDGOneDirectionKanComparisonMap A r C).hom ≫
            (show ((presentedPerfectDGBFBoundaryFunctor A r).obj C).obj ⟶
              (S.functor.obj C).obj from S.comparison C)) ≫
          curry (show _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (S.functor.obj C).obj ⟶
            ((presentedPerfectDGBFStepFunctor A r S.functor S.comparison S.naturality).obj C).obj
            from presentedPerfectDGBFStepStructureMap A r S.functor S.comparison
              S.naturality C)) =
      componentOf (presentedPerfectDGKanAssemblyRightAdjoint A r C ≫
        (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map
          (show ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj ⟶
            ((presentedPerfectDGBFStepFunctor A r S.functor S.comparison S.naturality).obj C).obj
            from presentedPerfectDGBFStepComparison A r S.functor S.comparison
              S.naturality C)) := by
  have h := pointedEnrichedCylinderCompletion_component_square
    (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGBFStepLeftTargetFunctor A S.functor)
    (presentedPerfectDGKanAssemblyTargetFunctor A r)
    (presentedPerfectDGBFStepLeftMap A r S.functor S.comparison)
    (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGBFStepLeft_whisker A r S.functor S.comparison S.naturality)
    (presentedPerfectDGKanAssemblyRight_whisker A r) C
  erw [presentedPerfectDGBFStepLeftMap_suspension A r S C] at h
  let l := (presentedPerfectDGOneDirectionKanComparisonMap A r C).hom ≫
    (show ((presentedPerfectDGBFBoundaryFunctor A r).obj C).obj ⟶
      (S.functor.obj C).obj from S.comparison C)
  let σ : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (S.functor.obj C).obj ⟶
      ((presentedPerfectDGBFStepFunctor A r S.functor S.comparison S.naturality).obj C).obj :=
    presentedPerfectDGBFStepStructureMap A r S.functor S.comparison S.naturality C
  let a : ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj :=
    presentedPerfectDGKanAssemblyRightMap A r C
  let d : ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGBFStepFunctor A r S.functor S.comparison S.naturality).obj C).obj :=
    presentedPerfectDGBFStepComparison A r S.functor S.comparison S.naturality C
  have hc := componentOf_curry h
  erw [curry_natural_left l σ, curry_natural_right a d] at hc
  exact hc

end SerrePositivity.KST.SConstruction
