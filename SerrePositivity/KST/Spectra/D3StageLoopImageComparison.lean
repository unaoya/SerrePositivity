module

public import SerrePositivity.KST.Spectra.D3StageLoopedCanonicalProjection

/-!
概要：次段 loop 像の標準比較と、元の次段比較の loop 像を全図式で接続する。
方針：厳密終点を共有する二つの標準図式を同じ fiber 内で比較し、終点の充満忠実性で反映。
規約：標準図式間の比較因子を保持する。その始点成分を恒等射とは扱わない。
使われ方：指定 BF 構造・既存段比較・次段比較の loop 像を結ぶ全図式正方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra

/-- 同じ端点の等式由来の同型は、同じ指定値を持つ。 -/
lemma d3FunctorEqIso_unique {A X : SSet.{u}} {f g : A ⟶ X}
    {e e' : FunctorIso f g} (he : F2.IsFunctorEqIso e) (he' : F2.IsFunctorEqIso e') :
    e = e' := by
  obtain ⟨h, he⟩ := he
  exact he.trans (he'.eq h).symm

namespace OmegaSpectrum.AdjointLoopRelativeBF

lemma commonChosenStageCanonicalImageFamily_target (n : ℕ) :
    commonChosenStageCanonicalImageFamily.{u} n ≫
      loopDiagramEvaluation PointedKanInfinity 1 1 =
    commonChosenStageLoopImageFamily n ≫ loopDiagramEvaluation PointedKanInfinity 1 1 :=
  d3LoopCanonicalFamily_target d3PointedKanLoopSection d3PointedKanLoopSection_target _

/-- 次段比較の loop 像と、同じ実次段像の標準図式は、元の厳密終点を共有する。 -/
lemma commonChosenStageLoopImageComparison_target_eq (n : ℕ) :
    commonChosenStageLoopedCanonicalFamily.{u} n ≫
      loopDiagramEvaluation PointedKanInfinity 1 1 =
    commonChosenStageCanonicalImageFamily n ≫
      loopDiagramEvaluation PointedKanInfinity 1 1 :=
  (commonChosenStageLoopedCanonicalFamily_target n).trans
    (commonChosenStageCanonicalImageFamily_target n).symm

/-- 二つの標準図式の比較を、指定された厳密終点の同じ実 fiber 内に保持する。 -/
def commonChosenStageLoopImageComparison (n : ℕ) :
    FunctorIso (commonChosenStageLoopedCanonicalFamily.{u} n)
      (commonChosenStageCanonicalImageFamily n) :=
  loopDiagramFamilyIso_of_section d3PointedKanLoopSection d3PointedKanLoopSection_target
    _ _ (commonChosenStageLoopImageComparison_target_eq n)

lemma commonChosenStageLoopImageComparison_target (n : ℕ) :
    (commonChosenStageLoopImageComparison.{u} n).postcomp
      (loopDiagramEvaluation PointedKanInfinity 1 1) =
    eqToIso (congrArg
      (fun a : SimplicialNerve CommonObject.{u} ⟶ PointedKanInfinity ↦
        SSet.HomotopyCategory.mk (functorVertex a))
      (commonChosenStageLoopImageComparison_target_eq n)) := by
  let := loopDiagramEvaluation_target_trivialKanFibration_of_section PointedKanInfinity
    d3PointedKanLoopSection d3PointedKanLoopSection_target
  exact functorIsoOfTrivialKanFibration_postcomp _ _ _
    (commonChosenStageLoopImageComparison_target_eq n)

/-- 次段像の標準比較は、元の次段比較の loop 像と同じ標準模型間比較の合成に一致。 -/
lemma commonChosenStageLoopImageComparison_triangle (n : ℕ) :
    commonChosenStageCanonicalImageDiagramIso.{u} n =
      commonChosenStageLoopedCanonicalDiagramIso n ≪≫ commonChosenStageLoopImageComparison n := by
  let := loopDiagramEvaluation_target_trivialKanFibration_of_section PointedKanInfinity
    d3PointedKanLoopSection d3PointedKanLoopSection_target
  let hf := isFullyFaithful_of_trivialKanFibration
    (loopDiagramEvaluation PointedKanInfinity 1 1)
  apply hf.postcomp_functorIso_injective
  rw [F2.functorIso_postcomp_trans]
  have h0 := d3IsFunctorEqIso_of_eqToIso _
    (commonChosenStageCanonicalImageFamily_target n).symm
    (d3LoopCanonicalDiagramIso_target d3PointedKanLoopSection
      d3PointedKanLoopSection_target (commonChosenStageLoopImageFamily n))
  have h1 := commonChosenStageLoopedCanonicalDiagramIso_target_isEq n
  have h2 := d3IsFunctorEqIso_of_eqToIso _
    (commonChosenStageLoopImageComparison_target_eq n)
    (commonChosenStageLoopImageComparison_target n)
  exact d3FunctorEqIso_unique h0 (h1.trans h2)

/-- 元の BF 構造の自然性を、次段比較の同じ loop 像と保持した模型比較へ接続する。 -/
lemma commonChosenStageLoopImageComparison_structure (n : ℕ) :
    commonChosenStageCanonicalDiagramIso.{u} n ≪≫ commonChosenStageCanonicalStructureIso n =
      (commonChosenStageStructureDiagramIso n ≪≫
        commonChosenStageLoopedCanonicalDiagramIso n) ≪≫
          commonChosenStageLoopImageComparison n := by
  rw [commonChosenStageCanonicalStructure_naturality,
    commonChosenStageLoopImageComparison_triangle, Iso.trans_assoc]

/-- 同じ全図式正方形を始点評価しても、標準模型間の比較因子をそのまま保持する。 -/
lemma commonChosenStageLoopImageComparison_source (n : ℕ) :
    (commonChosenStageCanonicalDiagramIso.{u} n).postcomp
        (loopDiagramEvaluation PointedKanInfinity 0 0) ≪≫
      (commonChosenStageCanonicalStructureIso n).postcomp
        (loopDiagramEvaluation PointedKanInfinity 0 0) =
    ((commonChosenStageStructureDiagramIso n).postcomp
        (loopDiagramEvaluation PointedKanInfinity 0 0) ≪≫
      (commonChosenStageLoopedCanonicalDiagramIso n).postcomp
        (loopDiagramEvaluation PointedKanInfinity 0 0)) ≪≫
      (commonChosenStageLoopImageComparison n).postcomp
        (loopDiagramEvaluation PointedKanInfinity 0 0) := by
  have h := congrArg (fun e ↦ FunctorIso.postcomp e
    (loopDiagramEvaluation PointedKanInfinity 0 0))
      (commonChosenStageLoopImageComparison_structure n)
  simpa only [F2.functorIso_postcomp_trans] using h

end OmegaSpectrum.AdjointLoopRelativeBF
end SerrePositivity.KST.Spectra
