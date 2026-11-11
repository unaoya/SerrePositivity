module

public import SerrePositivity.KST.LocalizingInvariants.BFFiberInfinityCone
public import SerrePositivity.KST.Spectra.CoherentCospanPresentation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinBoundary

/-!
概要：元の homotopyFiber を fiber 頂点とする実際の Sp の引き戻し四角形。
方針：通常の cospan の錐をホーンへ制限し、正方形の同型を使う。
規約：元の射の一単体と元の BF fiber 対象を保持する。使われ方：K-5 の長完全列の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberModel

local instance bfSquareSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance bfSquareHomKan (E B : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom E B) := OmegaSpectrum.mappingSpace_kanComplex E B

variable {E B : OmegaSpectrum.{u}} (f : E ⟶ B)

/-- 同じ BF 二射をホーンの二辺として持つ錐。 -/
def hornCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fromPoint B)).toTruncated) :=
  (DiagramLimitTransport.restrict (homotopyFiberCone f)
    CospanShape.strictCospanHornIso.inv).cast (CospanShape.strictDiagram_eq f (fromPoint B))

lemma hornCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (hornCone f) := by
  let d := homotopyFiberCone f
  let i := CospanShape.strictCospanHornIso.{u, u + 1}.inv
  have := DiagramLimitTransport.restriction_trivial
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram f (fromPoint B))) i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso CospanShape.strictCospanHornIso.symm)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram f (fromPoint B))) i)
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (DiagramLimitTransport.restrict d i) :=
    (e.isTerminalVertex_iff d).1 (homotopyFiberCone_isLimit f)
  exact hc.cast (CospanShape.strictDiagram_eq f (fromPoint B))

lemma hornCone_vertex : (hornCone f).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (homotopyFiber f) := by
  rw [hornCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, DiagramLimitTransport.vertex_restrict,
    homotopyFiberCone_vertex]

/-- 錐から四角形への変換は左下の fiber 頂点を保つ。 -/
lemma coneSquare_apex {X : SSet.{u}} {p : (horn 2 2 : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare c) 0 0 = c.vertex := by
  have hL := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_left.{u}
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 at hL
  have hh := congrArg (fun q ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom ≫ q) hL
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp] at hh
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (horn 2 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom =
      SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 := by
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] Δ[1] ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) horn₂₂.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom) := by
        simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
      _ = _ := by rw [hh, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inl_vertex]
  have hv : SSet.yonedaEquiv.symm
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (horn 2 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom := by
    rw [hj]
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    apply Prod.ext <;> decide
  have h := congrArg (fun k ↦ SSet.yonedaEquiv (k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ c.val))) hv
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at h
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq c).symm

/-- 元の任意射と元の homotopyFiber を保持する実 fiber 四角形。 -/
def homotopyFiberSquare : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated where
  square := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (hornCone f)
  zero_corner := by
    have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (hornCone f)) 0 1 =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.{u} := by
      rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopEdge_source, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_top, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan_right]
      exact (congrArg (fun v : Sp.{u} _⦋1⦌ ↦ Sp.{u}.δ 1 v)
        (SSet.yonedaEquiv.apply_symm_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fromPoint B)).edge)).trans
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fromPoint B)).src_eq
    exact hz.symm ▸ pointZeroVertex.isZero
  right_edge := by rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_right, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan_left]
  isPullback := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_isPullback _ (hornCone_isLimit f)

/-- 四角形の fiber は、長完全列で使う元の BF homotopyFiber の頂点である。 -/
lemma homotopyFiberSquare_vertex :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (homotopyFiberSquare f).square 0 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (homotopyFiber f) :=
  (coneSquare_apex (hornCone f)).trans (hornCone_vertex f)

end SerrePositivity.KST.LocalizingInvariants.FiberModel
