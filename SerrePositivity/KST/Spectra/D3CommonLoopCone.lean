module

public import SerrePositivity.KST.Spectra.D3CommonRefinement
public import SerrePositivity.KST.Spectra.D3LoopSourceCone
public import SerrePositivity.KST.Spectra.D3ConeForwardTransport

/-!
概要：共通 BF 対象を実始点とする loop 錐を、同じ共通左脚を保持して構成する。
方針：元の固定 cospan の slice に、指定左脚そのものを始端固定で持ち上げる。
規約：同じ tail・零角・比較辺を保つ。全 Hom に関する自然性は別工程。
使われ方：d3b② の共通 BF 解像と実 loop 図式の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance commonLoopConeSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance commonLoopConeHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 同じ共通 BF 左脚の可逆性。 -/
lemma commonLoopInclusion_isInvertible (X : OmegaSpectrum.{u}) :
    IsInvertibleEdge (coherentNerveEdge (commonLoopInclusion X)).toTruncated :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _ (commonLoopInclusion_levelwise X)

/-- 元の実錐から共通対象へ向かう辺は同じ BF 左脚。 -/
def commonLoopConeApexEdge (X : OmegaSpectrum.{u}) :
    Truncated.Edge (X := (truncation 2).obj Sp.{u})
      (loopSourceCone X).vertex (coherentNerveVertex (commonRefinement X)) :=
  ⟨(coherentNerveEdge (commonLoopInclusion X)).edge,
    (coherentNerveEdge (commonLoopInclusion X)).src_eq.trans (loopSourceCone_vertex X).symm,
    (coherentNerveEdge (commonLoopInclusion X)).tgt_eq⟩

lemma commonLoopConeApexEdge_isInvertible (X : OmegaSpectrum.{u}) :
    IsInvertibleEdge (commonLoopConeApexEdge X) :=
  (isInvertibleEdge_congr (e := commonLoopConeApexEdge X)
    (f := (coherentNerveEdge (commonLoopInclusion X)).toTruncated) rfl).2
      (commonLoopInclusion_isInvertible X)

/-- 元の実錐を始端とし、同じ共通左脚を射影に持つ実錐比較。 -/
def commonLoopConeLift (X : OmegaSpectrum.{u}) :
    (Δ[1] : SSet.{u + 1}) ⟶ sliceOver (BasedLoop.diagram (tail X)) :=
  Classical.choose (d3_rightFibration_liftEdge_source
    (sliceOverProjection (BasedLoop.diagram (tail X))) (loopSourceCone X)
    (commonLoopConeApexEdge X) (commonLoopConeApexEdge_isInvertible X))

lemma commonLoopConeLift_source (X : OmegaSpectrum.{u}) :
    stdSimplex.δ 1 ≫ commonLoopConeLift X = SSet.yonedaEquiv.symm (loopSourceCone X) :=
  (Classical.choose_spec (d3_rightFibration_liftEdge_source
    (sliceOverProjection (BasedLoop.diagram (tail X))) (loopSourceCone X)
    (commonLoopConeApexEdge X) (commonLoopConeApexEdge_isInvertible X))).1

/-- 射影は共通 BF 左脚の同じ一次単体。 -/
lemma commonLoopConeLift_projection (X : OmegaSpectrum.{u}) :
    commonLoopConeLift X ≫ sliceOverProjection (BasedLoop.diagram (tail X)) =
      SSet.yonedaEquiv.symm (coherentNerveEdge (commonLoopInclusion X)).edge :=
  (Classical.choose_spec (d3_rightFibration_liftEdge_source
    (sliceOverProjection (BasedLoop.diagram (tail X))) (loopSourceCone X)
    (commonLoopConeApexEdge X) (commonLoopConeApexEdge_isInvertible X))).2

/-- 共通対象上の、元の固定 cospan に対する実錐。 -/
def commonLoopCone (X : OmegaSpectrum.{u}) : JoinCone (BasedLoop.diagram (tail X)) :=
  (sliceOver (BasedLoop.diagram (tail X))).δ 0 (SSet.yonedaEquiv (commonLoopConeLift X))

def commonLoopConeEdge (X : OmegaSpectrum.{u}) :
    Truncated.Edge (X := (truncation 2).obj (sliceOver (BasedLoop.diagram (tail X))))
      (loopSourceCone X) (commonLoopCone X) :=
  ⟨SSet.yonedaEquiv (commonLoopConeLift X), by
    change (sliceOver (BasedLoop.diagram (tail X))).δ 1
      (SSet.yonedaEquiv (commonLoopConeLift X)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, commonLoopConeLift_source, Equiv.apply_symm_apply], rfl⟩

lemma commonLoopConeEdge_projection (X : OmegaSpectrum.{u}) :
    ((commonLoopConeEdge X).map
      ((truncation 2).map (sliceOverProjection (BasedLoop.diagram (tail X))))).edge =
      (coherentNerveEdge (commonLoopInclusion X)).edge := by
  change (sliceOverProjection (BasedLoop.diagram (tail X))).app _
    (SSet.yonedaEquiv (commonLoopConeLift X)) = _
  rw [← SSet.yonedaEquiv_comp, commonLoopConeLift_projection, Equiv.apply_symm_apply]

lemma commonLoopConeEdge_isInvertible (X : OmegaSpectrum.{u}) :
    IsInvertibleEdge (X := sliceOver (BasedLoop.diagram (tail X))) (commonLoopConeEdge X) :=
  derived_rightFibration_reflects_invertibleEdge
    (sliceOverProjection (BasedLoop.diagram (tail X))) (commonLoopConeEdge X)
    ((isInvertibleEdge_congr (commonLoopConeEdge_projection X)).2
      (commonLoopInclusion_isInvertible X))

/-- 同じ共通左脚を頂点成分とする錐全体の指定同型。 -/
def commonLoopConeIso (X : OmegaSpectrum.{u}) :
    VertexIso (X := sliceOver (BasedLoop.diagram (tail X)))
      (loopSourceCone X) (commonLoopCone X) := by
  haveI := commonLoopConeEdge_isInvertible X
  exact asIso (Truncated.HomotopyCategory.homMk (commonLoopConeEdge X))

lemma commonLoopCone_vertex (X : OmegaSpectrum.{u}) :
    (commonLoopCone X).vertex = coherentNerveVertex (commonRefinement X) := by
  have ht := congrArg (fun z ↦ Sp.δ 0 z) (commonLoopConeEdge_projection X)
  have hn := ConcreteCategory.congr_hom
    ((sliceOverProjection (BasedLoop.diagram (tail X))).naturality
      (SimplexCategory.δ (0 : Fin 2)).op)
    (SSet.yonedaEquiv (commonLoopConeLift X))
  exact hn.trans (ht.trans (coherentNerveEdge (commonLoopInclusion X)).tgt_eq)

lemma commonLoopCone_isLimit (X : OmegaSpectrum.{u}) : IsLimitCone (commonLoopCone X) :=
  (loopSourceCone_isLimit X).of_vertexIso (commonLoopConeIso X)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
