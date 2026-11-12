module

public import SerrePositivity.KST.Spectra.SpectrumPointLoopReference
public import SerrePositivity.KST.Spectra.StrictCospanHorn
public import SerrePositivity.KST.Spectra.DiagramLimitExistenceTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentConePointSection

/-!
概要：元の円評価錐を、元の通常の cospan の図式上で頂点固定の切断点として表示する。
方針：形状同型で元の錐全体を制限し、頂点固定の錐と切断点の標準全単射を使う。
規約：元の評価錐の全単体を保持。使われ方：companion の BK 切断点との最後の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance nativeCircleConeSectionSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 固定したホーン図式を元の通常の cospan の形状へ戻すと、元の strict 図式そのもの。 -/
lemma pointLoopCospan_strict (Y : OmegaSpectrum.{u}) :
    CospanShape.strictCospanHornIso.{u, u + 1}.hom ≫ pointLoopCospan Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (pointLoopDiagram Y) := by
  have h := congrArg (fun f ↦ CospanShape.strictCospanHornIso.{u, u + 1}.hom ≫ f)
    (CospanShape.strictDiagram_eq (fromPoint Y) (fromPoint Y))
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] at h
  exact h.symm

/-- 元の円評価錐の全体を、形状同型で元の通常の固定図式上へ戻したもの。 -/
def nativeCircleStrictCone (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)) :=
  (DiagramLimitTransport.restrict (nativeCirclePointLoopCone z)
    CospanShape.strictCospanHornIso.hom).cast
      (pointLoopCospan_strict (nativeCotensorInput PointedSimplicialSet.circle z).val)

/-- 元の円評価錐の頂点は、形状を戻しても元の cotensor の標準頂点。 -/
lemma nativeCircleStrictCone_vertex (z : Sp.{u} _⦋0⦌) :
    (nativeCircleStrictCone z).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
      (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val) := by
  rw [nativeCircleStrictCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, DiagramLimitTransport.vertex_restrict,
    nativeCirclePointLoopCone_vertex]

/-- 元の錐の左端の射も、元の cotensor の標準頂点に厳密固定される。 -/
lemma nativeCircleStrictCone_fixedVertex (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u + 1}) _ ≫ (nativeCircleStrictCone z).val =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
        (cotensor PointedSimplicialSet.circle
          (nativeCotensorInput PointedSimplicialSet.circle z).val)) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact nativeCircleStrictCone_vertex z

/-- 元の円評価錐全体を表す、同じ固定図式・固定頂点の切断空間の標準点。 -/
def nativeCircleStrictConeSectionPoint (z : Sp.{u} _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (pointLoopDiagram
        (nativeCotensorInput PointedSimplicialSet.circle z).val))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val))) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedVertexConeSpaceEquiv _ _
    ⟨nativeCircleStrictCone z, nativeCircleStrictCone_fixedVertex z⟩

/-- 標準点から錐を戻すと、元の円評価錐全体に厳密に戻る。 -/
lemma nativeCircleStrictConeSectionPoint_recover (z : Sp.{u} _⦋0⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedVertexConeSpaceEquiv _ _).symm (nativeCircleStrictConeSectionPoint z)).val =
      nativeCircleStrictCone z :=
  congrArg Subtype.val (Equiv.symm_apply_apply _ _)

private lemma cosliceSection_transport {K X : SSet.{u}} {p : K ⟶ X}
    {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {x : X _⦋0⦌} (h : c = d) (hc : c.vertex = x) (hd : d.vertex = x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection c ≫
        eqToHom (congrArg (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w)) hc) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection d ≫
        eqToHom (congrArg (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w)) hd) := by
  cases h
  rfl

/-- 元の錐全体の coslice 切断は、この標準点の実際の uncurry に厳密一致する。 -/
lemma nativeCircleStrictCone_cosliceSection (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection (nativeCircleStrictCone z) ≫
        eqToHom (congrArg (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w))
          (nativeCircleStrictCone_vertex z)) =
      inv (CartesianMonoidalCategory.fst _ (Δ[0] : SSet.{u + 1})) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (SSet.yonedaEquiv.symm (nativeCircleStrictConeSectionPoint z)) := by
  have hv := (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex (nativeCircleStrictConeSectionPoint_recover z)).trans
    (nativeCircleStrictCone_vertex z)
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedVertexConeSpaceEquiv_cosliceSection
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (pointLoopDiagram
      (nativeCotensorInput PointedSimplicialSet.circle z).val))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle
      (nativeCotensorInput PointedSimplicialSet.circle z).val))
    (nativeCircleStrictConeSectionPoint z) hv
  exact (cosliceSection_transport (nativeCircleStrictConeSectionPoint_recover z)
    hv (nativeCircleStrictCone_vertex z)).symm.trans h

end SerrePositivity.KST.Spectra.OmegaSpectrum
