module

public import SerrePositivity.KST.Spectra.D3StageStructureFunctor
public import SerrePositivity.InfinityCategories.Core.FunctorComposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition

/-!
概要：同じ実 loop 全四角形族の段間構造を、元の BF 構造随伴射の全図式同型で保持する。
方針：構造射の全関手同型を四角形の内部 Hom へ写し、元の全族へ前合成する。
規約：段比較を自由に選び直さない。BF 全体の自然同型の完成は別工程。
使われ方：共通 refined 段比較と実 loop 図式始点の段間整合の照合。
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

/-- 同じ次段全四角形へ通常 loop を作用させた、元の全単体の四角形族。 -/
def commonChosenStageLoopImageSquareFamily (n : ℕ) :
    SimplicialNerve CommonObject.{u} ⟶
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity :=
  commonChosenStageSquareFamily (n + 1) ≫
    (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map pointedKanLoopInfinity

/-- 元の BF 構造射は、同じ実全四角形族の段と次段 loop 像の全図式同型。 -/
def commonChosenStageStructureSquareIso (n : ℕ) :
    FunctorIso (commonChosenStageSquareFamily.{u} n)
      (commonChosenStageLoopImageSquareFamily n) := by
  have e := (d3StageStructureFunctorIso.{u} n).map_post
    ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])
  have h := e.precomp
    (commonChosenLoopDiagramFamily ≫ (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι)
  simpa only [commonChosenStageSquareFamily, commonChosenStageLoopImageSquareFamily,
    Functor.map_comp, Category.assoc] using h

/-- この同じ次段 loop 像の全族も、元の段との全図式同型から loop 性を保つ。 -/
lemma commonChosenStageLoopImageSquareFamily_isLoop (n : ℕ)
    (v : (SimplicialNerve CommonObject.{u}) _⦋0⦌) :
    IsLoopDiagramVertex ((commonChosenStageLoopImageSquareFamily n).app _ v) := by
  have e := (commonChosenStageStructureSquareIso.{u} n).toNatIso.app
    (SSet.HomotopyCategory.mk v)
  exact (d3IsLoopDiagramVertex_iso e).mp (commonChosenStageSquareFamily_isLoop n v)

/-- 同じ全 Hom・全単体を保持した、元の次段 loop 像の実 loop 図式族。 -/
def commonChosenStageLoopImageFamily (n : ℕ) :
    SimplicialNerve CommonObject.{u} ⟶ loopDiagrams PointedKanInfinity :=
  fullSubcomplexLift IsLoopDiagramVertex (commonChosenStageLoopImageSquareFamily n)
    (commonChosenStageLoopImageSquareFamily_isLoop n)

/-- 次段 loop 図式族の周囲の四角形は、元の同じ次段作用そのもの。 -/
lemma commonChosenStageLoopImageFamily_ι (n : ℕ) :
    commonChosenStageLoopImageFamily.{u} n ≫
      (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι =
        commonChosenStageLoopImageSquareFamily n := fullSubcomplexLift_ι _ _ _


/-- 同じ全四角形の構造同型を、両零角・普遍性を持つ全 loop 図式の同型へ戻す。 -/
def commonChosenStageStructureDiagramIso (n : ℕ) :
    FunctorIso (commonChosenStageLoopDiagramFamily.{u} n)
      (commonChosenStageLoopImageFamily n) := by
  apply (isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
      IsLoopDiagramVertex).preimageFunctorIso
  rw [commonChosenStageLoopImageFamily_ι]
  change FunctorIso ((fullSubcomplexLift IsLoopDiagramVertex (commonChosenStageSquareFamily n)
    (commonChosenStageSquareFamily_isLoop n)) ≫ _) _
  rw [fullSubcomplexLift_ι]
  exact commonChosenStageStructureSquareIso n

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
