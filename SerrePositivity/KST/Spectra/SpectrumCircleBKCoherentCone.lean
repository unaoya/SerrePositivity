module

public import SerrePositivity.KST.Spectra.SpectrumCircleBKReflectedPoints
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedHomHolimComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentConePointSection

/-!
概要：元の円 cotensor の恒等射の像から、固定図式上の実際の coherent な錐を構成する。
方針：反転 BK 切断点を共有の切断比較へ送り、頂点を固定した錐の全単射で戻す。
規約：頂点は元の cotensor。使われ方：この具体的な錐全体の族を用いる ∞ 極限性の証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleCoherentConeSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の反転 BK 切断点の射が表す、同じ end の実際の零単体。 -/
def circleBKReflectedEndPoint (Y : OmegaSpectrum.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y)
      (cotensor PointedSimplicialSet.circle Y) ⋙ SSet.opFunctor)) _⦋0⦌ :=
  SSet.unitHomEquiv _ (circleBKReflectedEndPointMap Y)

/-- 元の反転 BK 切断点の、固定図式全体上の coherent な切断点。 -/
def circleBKCoherentConePoint (Y : OmegaSpectrum.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (pointLoopDiagram Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle Y))) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison (pointLoopDiagram Y)
    (cotensor PointedSimplicialSet.circle Y)).app _ (ULift.up (circleBKReflectedEndPoint Y))

/-- 元の円評価の BK 切断点が与える、元の cotensor を頂点とする実際の coherent な錐。 -/
def circleBKCoherentCone (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (pointLoopDiagram Y)) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedVertexConeSpaceEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (pointLoopDiagram Y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle Y))).symm
      (circleBKCoherentConePoint Y)).val

/-- この錐の頂点は、元の円 cotensor の標準頂点に厳密一致する。 -/
lemma circleBKCoherentCone_vertex (Y : OmegaSpectrum.{u}) :
    (circleBKCoherentCone Y).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle Y) := by
  have h := ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedVertexConeSpaceEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (pointLoopDiagram Y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle Y))).symm
      (circleBKCoherentConePoint Y)).property
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] _ ≫ (circleBKCoherentCone Y).val) = _
  exact (congrArg SSet.yonedaEquiv h).trans (Equiv.apply_symm_apply _ _)

/-- 構成した錐の正規化した coslice 切断は、元の反転切断点の評価そのもの。 -/
lemma circleBKCoherentCone_cosliceSection (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection (circleBKCoherentCone Y) ≫
        eqToHom (congrArg (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w))
          (circleBKCoherentCone_vertex Y)) =
      inv (CartesianMonoidalCategory.fst _ (Δ[0] : SSet.{u + 1})) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (SSet.yonedaEquiv.symm (circleBKCoherentConePoint Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedVertexConeSpaceEquiv_cosliceSection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (pointLoopDiagram Y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor PointedSimplicialSet.circle Y)) (circleBKCoherentConePoint Y)
    (circleBKCoherentCone_vertex Y)

end SerrePositivity.KST.Spectra.OmegaSpectrum
