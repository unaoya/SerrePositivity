module

public import SerrePositivity.KST.Spectra.D3ReflectionSourceImage

/-!
概要：実段図式の反転を次段 loop 像と照合し、元の BF 構造との整合を証明する。
方針：同じ全図式の像に対する始点比較を、元の次段 loop 像と段構造へ実適用する。
規約：保持した模型補正との一致は別の未証明条件。段反転を自由に選び直さない。
使われ方：正しい構造補正を保つ BF 比較へ進むための、実反転候補の全段整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3StageReflectionSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の実段 loop 全図式を始点評価した、同じ指定反転。 -/
def commonChosenStageReflection (n : ℕ) :
    FunctorIso (commonChosenStageLoopDiagramFamily.{u} n ≫
      loopDiagramEvaluation PointedKanInfinity 0 0)
      (commonChosenStageLoopDiagramFamily n ≫ loopDiagramEvaluation PointedKanInfinity 0 0) :=
  (d3LoopDiagramReflection d3PointedKanLoopSection d3PointedKanLoopSection_target).precomp
    (commonChosenStageLoopDiagramFamily n)

/-- 同じ次段 loop 像の実全図式から得る指定反転。 -/
def commonChosenStageImageReflection (n : ℕ) :
    FunctorIso (commonChosenStageLoopImageFamily.{u} n ≫
      loopDiagramEvaluation PointedKanInfinity 0 0)
      (commonChosenStageLoopImageFamily n ≫ loopDiagramEvaluation PointedKanInfinity 0 0) :=
  (d3LoopDiagramReflection d3PointedKanLoopSection d3PointedKanLoopSection_target).precomp
    (commonChosenStageLoopImageFamily n)

/-- 全体の coherent な反転を段評価すると、元の同じ実段図式の反転を回収する。 -/
lemma commonChosenStageReflection_global (n : ℕ) :
    F2.functorIsoOfEq ((commonChosenLoopReflection.{u}).postcomp
      (coherentNerveMap (d3StageKanEnriched n)))
      (commonChosenStageLoopDiagramFamily_source n).symm
      (commonChosenStageLoopDiagramFamily_source n).symm =
    commonChosenStageReflection n := by
  exact d3LoopReflectionImage_source nativeLoopTargetEquivalence.inv
    nativeLoopTargetEquivalence_inv_target d3PointedKanLoopSection
    d3PointedKanLoopSection_target commonChosenLoopDiagramFamily
    (commonChosenStageLoopDiagramFamily n) (coherentNerveMap (d3StageKanEnriched n))
    (by rw [commonChosenStageLoopDiagramFamily_ι]; rfl)

/-- 同じ次段反転の通常 loop 像は、元の実次段 loop 像の反転と指定値で一致する。 -/
lemma commonChosenStageImageReflection_loop (n : ℕ) :
    F2.functorIsoOfEq ((commonChosenStageReflection.{u} (n + 1)).postcomp pointedKanLoopInfinity)
      (commonChosenStageLoopImageFamily_corner n 0 0).symm
      (commonChosenStageLoopImageFamily_corner n 0 0).symm =
    commonChosenStageImageReflection n := by
  exact d3LoopReflectionImage_source d3PointedKanLoopSection d3PointedKanLoopSection_target
    d3PointedKanLoopSection d3PointedKanLoopSection_target
    (commonChosenStageLoopDiagramFamily (n + 1)) (commonChosenStageLoopImageFamily n)
    pointedKanLoopInfinity (by
      rw [← Category.assoc, commonChosenStageLoopDiagramFamily_ι,
        commonChosenStageLoopImageFamily_ι]
      rfl)

/-- 実 BF 構造は、同じ段反転と次段反転の通常 loop 像に対して全関手空間で整合する。 -/
lemma commonChosenStageReflection_structure (n : ℕ) :
    (commonChosenStageStructureDiagramIso.{u} n).postcomp
        (loopDiagramEvaluation PointedKanInfinity 0 0) ≪≫
      F2.functorIsoOfEq ((commonChosenStageReflection (n + 1)).postcomp pointedKanLoopInfinity)
        (commonChosenStageLoopImageFamily_corner n 0 0).symm
        (commonChosenStageLoopImageFamily_corner n 0 0).symm =
    commonChosenStageReflection n ≪≫
      (commonChosenStageStructureDiagramIso n).postcomp
        (loopDiagramEvaluation PointedKanInfinity 0 0) := by
  rw [commonChosenStageImageReflection_loop]
  exact d3LoopDiagramReflection_naturality d3PointedKanLoopSection
    d3PointedKanLoopSection_target (commonChosenStageStructureDiagramIso n)

/-- 同じ実段反転は、全関手空間で二回合成が恒等となる。 -/
lemma commonChosenStageReflection_involution (n : ℕ) :
    commonChosenStageReflection.{u} n ≪≫ commonChosenStageReflection n = Iso.refl _ := by
  have h := congrArg (fun e ↦ FunctorIso.precomp e (commonChosenStageLoopDiagramFamily.{u} n))
    (d3LoopDiagramReflection_involution d3PointedKanLoopSection d3PointedKanLoopSection_target)
  rw [F2.functorIso_precomp_trans] at h
  have hr : (show FunctorIso (loopDiagramEvaluation PointedKanInfinity.{u} 0 0)
      (loopDiagramEvaluation PointedKanInfinity 0 0) from Iso.refl _).precomp
        (commonChosenStageLoopDiagramFamily n) = Iso.refl _ := by
    rw [F2.functorIso_precomp_eq_mapIso]
    exact Functor.mapIso_refl _ _
  rw [hr] at h
  exact h

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
