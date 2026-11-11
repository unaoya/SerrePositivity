module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFStage
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyAdjoint
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderComponents
public import SerrePositivity.KST.SConstruction.PointedCylinderOmegaCriterion

/-! # 元の前向き比較を保持する全正 BF 段の Ω 条件
概要：実際の既存段から作る同じ次段の構造随伴は全基点 π 同型。
方針：元の S₁ 比較と実円柱の基点固定四角形を随伴へ移す。
規約：全 Hom の自然性に逆射を選ばない。使われ方：実 BF 帰納列の Ω 条件。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet Spectra
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

/-- 帰納データの同じ実段の Kan 性を保持する。 -/
local instance presentedPerfectDGBFStageOmega_kanComplex (r : ℕ)
    (S : PresentedPerfectDGBFStage.{u, v} A r) (C : PerfDGInput.{u, v} A) :
    KanComplex (S.functor.obj C).obj.right := S.kan C

/-- 元の境界 Kan 値の同じ Kan 性。 -/
local instance presentedPerfectDGBFStepOmegaBoundary_kanComplex (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    KanComplex (((presentedPerfectDGBFBoundaryFunctor A r).obj C).obj).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _

/-- 元の一次方向 Kan 値の同じ Kan 性。 -/
local instance presentedPerfectDGBFStepOmegaSource_kanComplex (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    KanComplex (((presentedPerfectDGOneDirectionKanEnrichedFunctor A r).obj C).obj).right :=
  ((presentedPerfectDGOneDirectionKanEnrichedFunctor A r).obj C).property

/-- 同じ Ex∞ 源の Kan 性を標準点つき豊穣対象の型で保持する。 -/
local instance presentedPerfectDGBFStepOmegaRawSource_kanComplex (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    KanComplex ((coaugmentedPointedEnrichedFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit).obj
        ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C)).obj.right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _

/-- 次段の同じ Kan 性を実段の型で保持する。 -/
local instance presentedPerfectDGBFStepOmegaTarget_kanComplex (r : ℕ)
    (S : PresentedPerfectDGBFStage.{u, v} A r) (C : PerfDGInput.{u, v} A) :
    KanComplex
      (((presentedPerfectDGBFStepFunctor A r S.functor S.comparison
        S.naturality).obj C).obj).right :=
  presentedPerfectDGBFStep_kanComplex A r S.functor S.comparison S.naturality C

/-- 同じ次段の loop の Kan 性を閉構造の型で保持する。 -/
local instance presentedPerfectDGBFStepOmegaLoop_kanComplex (r : ℕ)
    (S : PresentedPerfectDGBFStage.{u, v} A r) (C : PerfDGInput.{u, v} A) :
    KanComplex ((ihom PointedSimplicialSet.circle.{max (u + 1) v}).obj
      ((presentedPerfectDGBFStepFunctor A r S.functor S.comparison
        S.naturality).obj C).obj).right :=
  loopSpace_kanComplex _

/-- 元の組み立て標的の loop は同じ実 Kan 複体。 -/
local instance presentedPerfectDGBFStepOmegaAssemblyLoop_kanComplex (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    KanComplex ((ihom pointedSSetCircleObject.{max (u + 1) v}.obj).obj
      ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj).right :=
  loopSpace_kanComplex _

/-- 同じ帰納段への前向き比較は全基点 π 同型。 -/
lemma presentedPerfectDGBFStageComparison_piIsomorphism (r : ℕ)
    (S : PresentedPerfectDGBFStage.{u, v} A r) (C : PerfDGInput.{u, v} A) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (show ((presentedPerfectDGBFBoundaryFunctor A r).obj C).obj ⟶
        (S.functor.obj C).obj from S.comparison C).right := by
  let _ : KanComplex (((presentedPerfectDGBFBoundaryFunctor A r).obj C).obj).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _
  exact kanPiIsomorphism_of_localized_isIso _ (S.weak C)

/-- 実左脚は、元の S₁ 比較と同じ前向き比較の合成の suspension。 -/
lemma presentedPerfectDGBFStepLeftMap_suspension (r : ℕ)
    (S : PresentedPerfectDGBFStage.{u, v} A r) (C : PerfDGInput.{u, v} A) :
    (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGBFStepLeftTargetFunctor A S.functor).obj C).obj from
        presentedPerfectDGBFStepLeftMap A r S.functor S.comparison C) =
      PointedSimplicialSet.circle.{max (u + 1) v} ◁
        ((presentedPerfectDGOneDirectionKanComparisonMap A r C).hom ≫
          (show ((presentedPerfectDGBFBoundaryFunctor A r).obj C).obj ⟶
            (S.functor.obj C).obj from S.comparison C)) := by
  change (PointedSimplicialSet.circle.{max (u + 1) v} ◁
    (presentedPerfectDGOneDirectionKanComparisonMap A r C).hom) ≫
      (PointedSimplicialSet.circle.{max (u + 1) v} ◁ _) = _
  exact (whiskerLeft_comp _ _ _).symm

/-- 同じ実円柱次段の元の構造随伴は全基点・全次数で π 同型。 -/
lemma presentedPerfectDGBFStepStructureAdjoint_piIsomorphism (r : ℕ)
    (S : PresentedPerfectDGBFStage.{u, v} A r) (C : PerfDGInput.{u, v} A) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (curry
      (show _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((S.functor.obj C).obj) ⟶
        ((presentedPerfectDGBFStepFunctor A r S.functor S.comparison S.naturality).obj C).obj
        from presentedPerfectDGBFStepStructureMap A r S.functor S.comparison
          S.naturality C)).right := by
  let l : ((presentedPerfectDGOneDirectionKanEnrichedFunctor A r).obj C).obj ⟶
      (S.functor.obj C).obj :=
    (presentedPerfectDGOneDirectionKanComparisonMap A r C).hom ≫ S.comparison C
  let a : ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj :=
    presentedPerfectDGKanAssemblyRightMap A r C
  let c : ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGBFStepFunctor A r S.functor S.comparison S.naturality).obj C).obj :=
    presentedPerfectDGBFStepComparison A r S.functor S.comparison S.naturality C
  have hl : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism l.right :=
    (presentedPerfectDGOneDirectionKanComparisonMap_piIsomorphism A r C).comp
      (presentedPerfectDGBFStageComparison_piIsomorphism A r S C)
  have ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (curry a).right :=
    presentedPerfectDGKanAssemblyRightAdjoint_piIsomorphism A r C
  have hc : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism c.right :=
    kanPiIsomorphism_of_localized_isIso _
      (presentedPerfectDGBFStepComparison_localized_isIso A r S.functor S.comparison
        S.naturality C (S.kan C) (S.weak C))
  apply cylinderAssemblyAdjoint_piIsomorphism l hl a ha c hc
  have h := pointedEnrichedCylinderCompletion_component_square
    (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGBFStepLeftTargetFunctor A S.functor)
    (presentedPerfectDGKanAssemblyTargetFunctor A r)
    (presentedPerfectDGBFStepLeftMap A r S.functor S.comparison)
    (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGBFStepLeft_whisker A r S.functor S.comparison S.naturality)
    (presentedPerfectDGKanAssemblyRight_whisker A r) C
  erw [presentedPerfectDGBFStepLeftMap_suspension A r S C] at h
  exact h

end SerrePositivity.KST.SConstruction
