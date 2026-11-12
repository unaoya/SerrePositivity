module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativePastingBoundaries

/-! # 貼った交換セルの一境界と前段の元の補正 trace
概要：全交換セルの一側の境界を、前段の元の前半補正の構造射による像へ照合する。
方針：suspension Hom の標的自然性と後合成の合成保存を全区間に適用する。
規約：前段の補正の全区間・順序を保持する。
使われ方：前段の前後半の全 trace を合わせる実二次元比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra

open scoped Simplicial
local instance nativePreviousTracePointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 交換全正方形の一面の全 trace は、前段の同じ前半補正の構造射による像。 -/
lemma monicKPrismCompatibilityInterchangeTrace_one_step (n : ℕ) :
    monicKPrismCompatibilityInterchangeTrace F f g n
      (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map g) n ≫
        (kKanSequence (F.obj z)).sigma n) =
      (monicKPrismCompositeFirstTrace F f g n).map
        (· ≫ RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) := by
  simp only [monicKPrismCompatibilityInterchangeTrace, monicKPrismCompositeFirstTrace,
    List.map_map, Function.comp_def]
  congr 1
  funext h
  dsimp only [RawSpectrumMapping.step]
  have hs := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.suspensionHom_post ((kOmegaSpectrum (F.obj x)).level n).space
    (kKanSequenceLevelMap (F.map g) n)
  change (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
      (kKanSequenceLevelMap (F.map g) n)).right ≫
      (suspensionHom ((kOmegaSpectrum (F.obj x)).level n).space
        ((kKanSequence (F.obj z)).level n).space).right =
    (suspensionHom ((kOmegaSpectrum (F.obj x)).level n).space
        ((kKanSequence (F.obj y)).level n).space).right ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level n).space)
        (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map g) n)).right at hs
  calc
    _ = (fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ▷
        (Δ[1] : SSet.{u})) ≫ h ≫
        (suspensionHom ((kOmegaSpectrum (F.obj x)).level n).space
          ((kKanSequence (F.obj y)).level n).space).right ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level n).space)
          (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map g) n)).right ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level n).space)
          ((kKanSequence (F.obj z)).sigma n)).right := by
      simp only [← PointedEnrichment.whiskerLeft_eq, eHomWhiskerLeft_comp]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun q =>
        (fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ▷
          (Δ[1] : SSet.{u})) ≫ h ≫ q ≫
          (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level n).space)
            ((kKanSequence (F.obj z)).sigma n)).right) hs.symm

/-- 貼り合わせ複体の一境界は、前段の元の前半 trace 全体の同じ構造射の像。 -/
lemma monicKPrismNativePastingMap_cells_one_previous_trace (n : ℕ) :
    (monicKPrismNativePastingCells F f g n).map (fun q =>
      (SSet.ι₁ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫
        q ≫ monicKPrismNativePastingMap F f g n) =
      (monicKPrismCompositeFirstTrace F f g n).map (fun h =>
        (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ h ≫
          RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) := by
  rw [monicKPrismNativePastingMap_cells_one_trace,
    monicKPrismCompatibilityInterchangeTrace_one_step]
  simp only [List.map_map, Function.comp_def]

end SerrePositivity.KST.SConstruction
