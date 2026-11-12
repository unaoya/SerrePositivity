module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFStepWeakEquivalence
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFFirstProperties
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.StrictSimplicialTransformationWhisker

/-! # 元の前向き弱比較を保持する実 BF 帰納データ
概要：Bᵣ→K_(r+1) と Kan 性・全 Hom 自然性・弱比較を同じ帰納データに保持する。
方針：最初の実円柱段を基底とし、実際の ΣK を使う同じ次段構成を反復する。
規約：未証明の Ω 条件をデータに要求しない。使われ方：厳密豊穣 BF 列の実段。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

/-- 元の Bᵣ からの前向き弱比較を備えた、実際の正の BF 段。 -/
structure PresentedPerfectDGBFStage (r : ℕ) where
  functor : EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
    PointedSSetObject.{max (u + 1) v}
  comparison : ∀ X, (presentedPerfectDGBFBoundaryFunctor A r).obj X ⟶ functor.obj X
  naturality : ∀ X Y, (presentedPerfectDGBFBoundaryFunctor A r).map X Y ≫
      eHomWhiskerLeft SSet ((presentedPerfectDGBFBoundaryFunctor A r).obj X) (comparison Y) =
    functor.map X Y ≫ eHomWhiskerRight SSet (comparison X) (functor.obj Y)
  kan : ∀ X, KanComplex (functor.obj X).obj.right
  weak : ∀ X, IsIso (AnodyneHomotopy.anodyneQ.map
    (show ((presentedPerfectDGBFBoundaryFunctor A r).obj X).obj ⟶ (functor.obj X).obj from
      comparison X).right)

/-- 同じ元の評価を単射化した最初の段を、実帰納データへ束ねる。 -/
def presentedPerfectDGBFInitialStage : PresentedPerfectDGBFStage.{u, v} A 0 where
  functor := presentedPerfectDGBFFirstFunctor A
  comparison := presentedPerfectDGBFFirstComparison A
  naturality := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformation_whisker _ _
    (presentedPerfectDGBFFirstComparisonTransformation A)
    (presentedPerfectDGBFFirstComparison A)
    (presentedPerfectDGBFFirstComparisonTransformation_app A)
  kan := presentedPerfectDGBFFirst_kanComplex A
  weak X := (Localization.inverts _ anodyneExtensions) _
    (presentedPerfectDGBFFirstComparison_anodyne A X)

/-- 実際の既存段の suspension を使う次段は、同じ全帰納不変条件を満たす。 -/
def presentedPerfectDGBFNextStage (r : ℕ) (S : PresentedPerfectDGBFStage.{u, v} A r) :
    PresentedPerfectDGBFStage.{u, v} A (r + 1) where
  functor := presentedPerfectDGBFStepFunctor A r S.functor S.comparison S.naturality
  comparison := presentedPerfectDGBFStepComparison A r S.functor S.comparison S.naturality
  naturality := presentedPerfectDGBFStepComparison_whisker A r S.functor S.comparison S.naturality
  kan := presentedPerfectDGBFStep_kanComplex A r S.functor S.comparison S.naturality
  weak X := presentedPerfectDGBFStepComparison_localized_isIso A r S.functor S.comparison
    S.naturality X (S.kan X) (S.weak X)

/-- 同じ元の最初の段から再帰する、全ての正の実 BF 段。 -/
def presentedPerfectDGBFPositiveStage : (r : ℕ) → PresentedPerfectDGBFStage.{u, v} A r
  | 0 => presentedPerfectDGBFInitialStage A
  | r + 1 => presentedPerfectDGBFNextStage A r (presentedPerfectDGBFPositiveStage r)

end SerrePositivity.KST.SConstruction
