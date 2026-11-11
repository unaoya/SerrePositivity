module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOAAssembly
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFStepAdjointComponent
public import SerrePositivity.KST.SConstruction.PointedComponentAssemblyTransfer

/-! # 旧 SOA K と新 BF K の全正構造随伴の比較
概要：全正段の前向き比較は元の構造随伴と点つき成分で可換。
方針：元の S₁ 比較の逆律と二 Kan 模型の比較四角形を実円柱四角形へ合成する。
規約：点ごとの弱比較であり豊穣関手を選び直さない。使われ方：実スペクトル比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet Spectra
open Spectra.PointedMapping SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 全正段の元の前向き比較は、旧・新構造随伴を点つき成分で結ぶ。 -/
lemma presentedPerfectDGBFRawSOAComparison_positive_adjoint (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    componentOf (presentedPerfectDGBFRawSOAComparison A C (r + 1) ≫
        curry ((presentedPerfectDGBFOmegaSpectrum A C).sigma (r + 1))) =
      componentOf (boundaryKanAssemblyAdjoint r
          (stableCategoryModel (presentedPerfectDGStableCategory A C)) ≫
        (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map
          (presentedPerfectDGBFRawSOAComparison A C (r + 2))) := by
  let X := stableCategoryModel (presentedPerfectDGStableCategory A C)
  let S := presentedPerfectDGBFPositiveStage A r
  let L := PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}
  let q := (oneDirectionKanComparisonNat r).app X
  let g := oneDirectionKanComparisonInverse r X
  let α := presentedPerfectDGBFSourceSOAComparison A r C
  let β := presentedPerfectDGBFBoundarySOAComparison A r C
  let β' := presentedPerfectDGBFBoundarySOAComparison A (r + 1) C
  let q' := (presentedPerfectDGOneDirectionKanComparisonMap A r C).hom
  let c : ((presentedPerfectDGBFBoundaryFunctor A r).obj C).obj ⟶
      (S.functor.obj C).obj := S.comparison C
  let s : (S.functor.obj C).obj ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace
      ((presentedPerfectDGBFStepFunctor A r S.functor S.comparison S.naturality).obj C).obj :=
    curry (show _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (S.functor.obj C).obj ⟶
      ((presentedPerfectDGBFStepFunctor A r S.functor S.comparison S.naturality).obj C).obj
      from presentedPerfectDGBFStepStructureMap A r S.functor S.comparison S.naturality C)
  let d : ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGBFStepFunctor A r S.functor S.comparison S.naturality).obj C).obj :=
    presentedPerfectDGBFStepComparison A r S.functor S.comparison S.naturality C
  let w := (kanAssemblyAdjointChoices_isContractibleKan r X).nonempty.some
  let a := kanAssemblyAdjointAt r X w
  let a' := presentedPerfectDGKanAssemblyRightAdjoint A r C
  have hi : componentOf (g ≫ q) = componentOf (𝟙 _) :=
    ((piZero_eq_iff_pointedHomotopy _ _).mpr
      (oneDirectionKanComparisonInverse_homotopy r X)).symm
  have hq : componentOf (α ≫ q') = componentOf (q ≫ β) :=
    pointedSOAExInfinityComparison_naturality_component
      (presentedPerfectDGOneDirectionPointedComparisonMap A r C)
  have ha : componentOf (α ≫ a') = componentOf (a ≫ L.map β') :=
    presentedPerfectDGBFSOAAssemblyAdjoint_component A r C w
  have hs : componentOf ((q' ≫ c) ≫ s) = componentOf (a' ≫ L.map d) :=
    presentedPerfectDGBFStepAdjoint_component A r S C
  have ht := pointedComponentAssemblyTransfer q g α β q' c s a a'
    (L.map β') (L.map d) hi hq ha hs
  change componentOf ((β ≫ c) ≫ s) = componentOf ((g ≫ a) ≫ L.map (β' ≫ d))
  erw [L.map_comp]
  exact (congrArg componentOf (Category.assoc β c s)).trans ht

end SerrePositivity.KST.SConstruction
