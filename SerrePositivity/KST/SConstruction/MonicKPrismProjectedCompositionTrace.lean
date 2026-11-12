module
public import SerrePositivity.KST.SConstruction.MonicKPrismCompatibilityInterchange
public import SerrePositivity.KST.SConstruction.FamilyChainInterchangeGluing

/-! # 合成補正の前半の射影と元の適合面の照合
概要：前の射の補正を後合成した trace の構造射での射影を、元の適合区間と交換面へ分解する。
方針：前後合成の交換と保存済みの全射影 trace を使い、残りを実交換正方形の零面へ同定する。
規約：元の全精密化パラメータと実円柱の順序を保つ。
使われ方：K の合成面に必要な、構造射で射影した実補正の二次元比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping SerrePositivity.InfinityCategories
open scoped Simplicial
local instance projectedCompositionTraceSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 点つき写像空間の通常の前後合成は、全族について厳密に交換する。 -/
lemma pointedMapping_post_pre {A B R S : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (g : R ⟶ S) :
    (PointedObject.basedHomMap B g).right ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i S =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i R ≫ (PointedObject.basedHomMap A g).right := by
  simp only [← PointedEnrichment.whiskerLeft_eq, ← PointedEnrichment.whiskerRight_eq]
  exact eHom_whisker_exchange SSet i g

variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 保存済みの各段の補正を射影すると、元の適合円柱と前段の同じ全補正になる。 -/
lemma monicKPrismTracedStage_projection_trace (n : ℕ) :
    (familyHomotopyChainTrace (monicKPrismTracedStage F f (n + 1)).chain).map
      (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
        ((kKanSequence (F.obj y)).level (n + 1)).space) =
      (monicKPrismRawSequenceCompatibility n F f).h ::
        (familyHomotopyChainTrace (monicKPrismTracedStage F f n).chain).map
          (· ≫ RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj y)) n) := by
  simpa only [monicKPrismTracedStage] using
    prescribedSequenceFamilyStage_trace (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f)) (fun n => monicKPrismRawLevelFamily n F f)
      (fun n => monicKPrismRawSequenceCompatibility n F f) (monicKPrismTracedBoundary F f) n

/-- 前半補正の射影は、元の前の適合区間と交換正方形の零面の全区間列である。 -/
lemma monicKPrismCompositeFirstTrace_projection (n : ℕ) :
    (monicKPrismCompositeFirstTrace F f g (n + 1)).map
      (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
        ((kKanSequence (F.obj z)).level (n + 1)).space) =
      ((fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ▷
        (Δ[1] : SSet.{u})) ≫ (monicKPrismRawSequenceCompatibility n F f).h ≫
          (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level n).space)
            (kKanSequenceLevelMap (F.map g) (n + 1))).right) ::
      monicKPrismCompatibilityInterchangeTrace F f g n
        ((kKanSequence (F.obj y)).sigma n ≫ kKanSequenceLevelMap (F.map g) (n + 1)) := by
  let P := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)
  let Q := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)
  let q := (PointedObject.basedHomMap
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level n).space)
      (kKanSequenceLevelMap (F.map g) (n + 1))).right
  have he := pointedMapping_post_pre ((kOmegaSpectrum (F.obj x)).sigma n)
    (kKanSequenceLevelMap (F.map g) (n + 1))
  calc
    _ = ((familyHomotopyChainTrace (monicKPrismTracedStage F f (n + 1)).chain).map
        (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
          ((kKanSequence (F.obj y)).level (n + 1)).space)).map
        (fun h => (fst P Q ▷ (Δ[1] : SSet.{u})) ≫ h ≫ q) := by
      simp only [monicKPrismCompositeFirstTrace, List.map_map, Function.comp_def,
        Category.assoc, he]
      rfl
    _ = ((fst P Q ▷ (Δ[1] : SSet.{u})) ≫ (monicKPrismRawSequenceCompatibility n F f).h ≫ q) ::
        (familyHomotopyChainTrace (monicKPrismTracedStage F f n).chain).map
          (fun h => (fst P Q ▷ (Δ[1] : SSet.{u})) ≫ h ≫
            RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj y)) n ≫ q) := by
      rw [monicKPrismTracedStage_projection_trace]
      simp only [List.map_cons, List.map_map, Function.comp_def, Category.assoc]
      rfl
    _ = _ := by
      congr 1
      dsimp only [monicKPrismCompatibilityInterchangeTrace]
      congr 1
      funext h
      dsimp only [q, RawSpectrumMapping.step]
      simp only [Category.assoc, ← PointedEnrichment.whiskerLeft_eq, eHomWhiskerLeft_comp]
      rfl

/-- 射影した前半の残り全区間は、元の実交換正方形列の零面そのものである。 -/
lemma monicKPrismCompositeFirstTrace_projection_squares (n : ℕ) :
    (monicKPrismCompositeFirstTrace F f g (n + 1)).map
      (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
        ((kKanSequence (F.obj z)).level (n + 1)).space) =
      ((fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ▷
        (Δ[1] : SSet.{u})) ≫ (monicKPrismRawSequenceCompatibility n F f).h ≫
          (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level n).space)
            (kKanSequenceLevelMap (F.map g) (n + 1))).right) ::
      (monicKPrismCompatibilityInterchangeSquares F f g n).map (SSet.ι₀ ≫ ·) := by
  rw [monicKPrismCompositeFirstTrace_projection,
    monicKPrismCompatibilityInterchangeSquares_second_zero]

/-- 元の K の交換正方形列も、共有面の同じ全円柱に沿って厳密に貼り合う。 -/
lemma monicKPrismCompatibilityInterchangeSquares_glue (n : ℕ) :
    List.IsChain (fun s t =>
      (SSet.ι₁ (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⊗ nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ▷
        (Δ[1] : SSet.{u})) ≫ s =
      (SSet.ι₀ (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⊗ nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ▷
        (Δ[1] : SSet.{u})) ≫ t) (monicKPrismCompatibilityInterchangeSquares F f g n) := by
  unfold monicKPrismCompatibilityInterchangeSquares pointedCompatibilityInterchangeSquares
  exact familyHomotopyChainInterchangeSquares_glue _ _ _

end SerrePositivity.KST.SConstruction
