module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFStage
public import SerrePositivity.KST.Spectra.KanSequence

/-! # 厳密 dg 入力上の全実 BF 帰納列
概要：零段 ΩB₀ と全ての正の実段を、元の単射構造射を持つ Kan 列へ束ねる。
方針：最初の評価の単射置換と、実際の既存段を左標的とする次段を再帰する。
規約：Ω 条件は別工程。使われ方：厳密豊穣スペクトル値 K の実段と構造射。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ元の ΩB₀ を零段とし、全ての実正段を持つ厳密豊穣関手族。 -/
def presentedPerfectDGBFLevelFunctor : (n : ℕ) →
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v}
  | 0 => presentedPerfectDGBFZeroFunctor A
  | r + 1 => (presentedPerfectDGBFPositiveStage A r).functor

/-- 同じ全実段の元の suspension 構造射。 -/
def presentedPerfectDGBFStructureMap : (n : ℕ) → (X : PerfDGInput.{u, v} A) →
    ((presentedPerfectDGBFLevelFunctor A n).comp SSet
      (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v})).obj X ⟶
      (presentedPerfectDGBFLevelFunctor A (n + 1)).obj X
  | 0, X => presentedPerfectDGBFFirstStructureMap A X
  | r + 1, X => presentedPerfectDGBFStepStructureMap A r
      (presentedPerfectDGBFPositiveStage A r).functor
      (presentedPerfectDGBFPositiveStage A r).comparison
      (presentedPerfectDGBFPositiveStage A r).naturality X

/-- 同じ全ての実段は Kan 複体。 -/
lemma presentedPerfectDGBFLevel_kanComplex (n : ℕ) (X : PerfDGInput.{u, v} A) :
    KanComplex (((presentedPerfectDGBFLevelFunctor A n).obj X).obj).right := by
  cases n with
  | zero => exact presentedPerfectDGBFZero_kanComplex A X
  | succ r => exact (presentedPerfectDGBFPositiveStage A r).kan X

/-- 同じ全ての実構造射は、基礎単体集合上で単射。 -/
lemma presentedPerfectDGBFStructureMap_mono (n : ℕ) (X : PerfDGInput.{u, v} A) :
    Mono (show _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (((presentedPerfectDGBFLevelFunctor A n).obj X).obj) ⟶
      ((presentedPerfectDGBFLevelFunctor A (n + 1)).obj X).obj from
        presentedPerfectDGBFStructureMap A n X).right := by
  cases n with
  | zero => exact presentedPerfectDGBFFirstStructureMap_mono A X
  | succ r =>
      exact presentedPerfectDGBFStepStructureMap_mono A r
        (presentedPerfectDGBFPositiveStage A r).functor
        (presentedPerfectDGBFPositiveStage A r).comparison
        (presentedPerfectDGBFPositiveStage A r).naturality X

/-- 同じ全ての実構造射は、全厳密 dg 入力 Hom に自然。 -/
lemma presentedPerfectDGBFStructureMap_whisker (n : ℕ) (X Y : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGBFLevelFunctor A n).comp SSet
        (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v})).map X Y ≫
        eHomWhiskerLeft SSet
          (((presentedPerfectDGBFLevelFunctor A n).comp SSet
            (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v})).obj X)
          (presentedPerfectDGBFStructureMap A n Y) =
      (presentedPerfectDGBFLevelFunctor A (n + 1)).map X Y ≫
        eHomWhiskerRight SSet (presentedPerfectDGBFStructureMap A n X)
          ((presentedPerfectDGBFLevelFunctor A (n + 1)).obj Y) := by
  cases n with
  | zero =>
      exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformation_whisker _ _
        (presentedPerfectDGBFFirstStructureTransformation A)
        (presentedPerfectDGBFFirstStructureMap A)
        (presentedPerfectDGBFFirstStructureTransformation_app A) X Y
  | succ r =>
      exact presentedPerfectDGBFStepStructureMap_whisker A r
        (presentedPerfectDGBFPositiveStage A r).functor
        (presentedPerfectDGBFPositiveStage A r).comparison
        (presentedPerfectDGBFPositiveStage A r).naturality X Y

/-- 同じ全構造射を、厳密 dg 入力上の厳密豊穣自然変換に束ねる。 -/
def presentedPerfectDGBFStructureTransformation (n : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      ((presentedPerfectDGBFLevelFunctor A n).comp SSet
        (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v}))
      (presentedPerfectDGBFLevelFunctor A (n + 1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _ (presentedPerfectDGBFStructureMap A n)
    (presentedPerfectDGBFStructureMap_whisker A n)

/-- 同じ全構造変換の成分は、元の同じ実構造射。 -/
lemma presentedPerfectDGBFStructureTransformation_app (n : ℕ) (X : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBFStructureTransformation A n).app X =
      eHomEquiv SSet (presentedPerfectDGBFStructureMap A n X) := rfl

/-- 同じ実段と構造射を持つ実際の Kan 列。Ω 条件はここには含めない。 -/
def presentedPerfectDGBFKanSequence (X : PerfDGInput.{u, v} A) :
    KanSequence.{max (u + 1) v} where
  level n := ⟨((presentedPerfectDGBFLevelFunctor A n).obj X).obj,
    presentedPerfectDGBFLevel_kanComplex A n X⟩
  sigma n := presentedPerfectDGBFStructureMap A n X

/-- 同じ実 Kan 列の零段は、元の零次境界 Kan 商の loop そのもの。 -/
lemma presentedPerfectDGBFKanSequence_zero (X : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGBFKanSequence A X).level 0).space =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((presentedPerfectDGBoundaryKanEnrichedFunctor A 0).obj X).obj := rfl

end SerrePositivity.KST.SConstruction
