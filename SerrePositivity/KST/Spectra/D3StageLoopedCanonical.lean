module

public import SerrePositivity.KST.Spectra.D3CommonStageCanonicalCoherence

/-!
概要：既存の実段図式比較を通常 loop で写し、同じ全図式比較として保持する。
方針：周囲の全四角形へ同じ後合成を施し、既存の次段 loop 像との同型で loop 性を認証。
規約：loop の全図式保存を新仮定にせず、この同じ像と比較から認証する。
使われ方：次段 loop 像の比較と、次段比較の loop 像の接続。
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

/-- 元の標準族の次段へ、同じ通常 loop を施した全四角形族。 -/
def commonChosenStageLoopedCanonicalSquareFamily (n : ℕ) :
    SimplicialNerve CommonObject.{u} ⟶
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity :=
  (commonChosenStageCanonicalFamily (n + 1) ≫
    (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι) ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map pointedKanLoopInfinity

/-- 同じ既存の次段図式比較を通常 loop で写した、全四角形の指定同型。 -/
def commonChosenStageLoopedCanonicalSquareIso (n : ℕ) :
    FunctorIso (commonChosenStageLoopImageSquareFamily.{u} n)
      (commonChosenStageLoopedCanonicalSquareFamily n) :=
  F2.functorIsoOfEq
    ((commonChosenStageCanonicalDiagramIso (n + 1)).postcomp
      ((fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫
        (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map pointedKanLoopInfinity))
    (by simp only [commonChosenStageLoopImageSquareFamily,
      ← commonChosenStageLoopDiagramFamily_ι, Category.assoc])
    (by simp only [commonChosenStageLoopedCanonicalSquareFamily, Category.assoc])

/-- この同じ loop 像の標準図式は、元の実次段像との全図式同型から loop 性を持つ。 -/
lemma commonChosenStageLoopedCanonicalSquareFamily_isLoop (n : ℕ)
    (v : (SimplicialNerve CommonObject.{u}) _⦋0⦌) :
    IsLoopDiagramVertex ((commonChosenStageLoopedCanonicalSquareFamily n).app _ v) := by
  have e := (commonChosenStageLoopedCanonicalSquareIso n).toNatIso.app
    (SSet.HomotopyCategory.mk v)
  exact (d3IsLoopDiagramVertex_iso e).mp (commonChosenStageLoopImageSquareFamily_isLoop n v)

/-- 元の標準族へ通常 loop を施した同じ全族を、実 loop 図式族へ因子化する。 -/
def commonChosenStageLoopedCanonicalFamily (n : ℕ) :
    SimplicialNerve CommonObject.{u} ⟶ loopDiagrams PointedKanInfinity :=
  fullSubcomplexLift IsLoopDiagramVertex (commonChosenStageLoopedCanonicalSquareFamily n)
    (commonChosenStageLoopedCanonicalSquareFamily_isLoop n)

lemma commonChosenStageLoopedCanonicalFamily_ι (n : ℕ) :
    commonChosenStageLoopedCanonicalFamily.{u} n ≫
      (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι =
        commonChosenStageLoopedCanonicalSquareFamily n := fullSubcomplexLift_ι _ _ _

/-- 同じ次段比較の loop 像を、実 loop 全図式の指定同型として回収する。 -/
def commonChosenStageLoopedCanonicalDiagramIso (n : ℕ) :
    FunctorIso (commonChosenStageLoopImageFamily.{u} n)
      (commonChosenStageLoopedCanonicalFamily n) :=
  (isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
      IsLoopDiagramVertex).preimageFunctorIso
    (F2.functorIsoOfEq (commonChosenStageLoopedCanonicalSquareIso n)
      (commonChosenStageLoopImageFamily_ι n).symm
      (commonChosenStageLoopedCanonicalFamily_ι n).symm)

/-- 同じ通常 loop 像の各角は、元の標準族の同じ角の loop そのもの。 -/
lemma commonChosenStageLoopedCanonicalFamily_corner (n : ℕ) (i j : Fin 2) :
    commonChosenStageLoopedCanonicalFamily.{u} n ≫
      loopDiagramEvaluation PointedKanInfinity i j =
    (commonChosenStageCanonicalFamily (n + 1) ≫
      loopDiagramEvaluation PointedKanInfinity i j) ≫ pointedKanLoopInfinity := by
  dsimp only [loopDiagramEvaluation]
  rw [← Category.assoc, commonChosenStageLoopedCanonicalFamily_ι]
  dsimp only [commonChosenStageLoopedCanonicalSquareFamily]
  rw [Category.assoc, d3SquareEvaluation_postcomp]
  simp only [Category.assoc]

/-- 元の実次段 loop 像も、各角で元の実次段の同じ loop を回収する。 -/
lemma commonChosenStageLoopImageFamily_corner (n : ℕ) (i j : Fin 2) :
    commonChosenStageLoopImageFamily.{u} n ≫ loopDiagramEvaluation PointedKanInfinity i j =
    (commonChosenStageLoopDiagramFamily (n + 1) ≫
      loopDiagramEvaluation PointedKanInfinity i j) ≫ pointedKanLoopInfinity := by
  dsimp only [loopDiagramEvaluation]
  rw [← Category.assoc, commonChosenStageLoopImageFamily_ι]
  dsimp only [commonChosenStageLoopImageSquareFamily]
  rw [← commonChosenStageLoopDiagramFamily_ι]
  rw [Category.assoc, d3SquareEvaluation_postcomp]
  simp only [Category.assoc]

/-- 既存の次段比較の同じ通常 loop 像は、同じ元の厳密終点を保つ。 -/
lemma commonChosenStageLoopedCanonicalFamily_target (n : ℕ) :
    commonChosenStageLoopedCanonicalFamily.{u} n ≫
      loopDiagramEvaluation PointedKanInfinity 1 1 =
    commonChosenStageLoopImageFamily n ≫ loopDiagramEvaluation PointedKanInfinity 1 1 := by
  rw [commonChosenStageLoopedCanonicalFamily_corner, commonChosenStageLoopImageFamily_corner,
    commonChosenStageCanonicalFamily_target]

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
