module

public import SerrePositivity.KST.Spectra.SpectrumCircleCompanionEdgewiseTetrahedra
public import SerrePositivity.KST.Spectra.WeightedEdgewiseSectionTriangle

/-!
概要：元の companion の共通解像切断が作る weighted 錐の三角形を、同じ三単体へ照合する。
方針：全切断の左射影と、元の初区間での triangleTrace の式を使う。
規約：中央の Hom を恒等に保つ。使われ方：元の coherent 錐の切断点と符号の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance companionReflectedTrianglesSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance companionReflectedTrianglesHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

/-- 元の共通解像の全切断を左射影した、同じ Hom の反転係数上の全切断。 -/
def circleCompanionBKReflectedSection (z : Sp.{u} _⦋0⦌) :=
  circleCompanionBKEdgewiseSection z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.diagramEdgewiseLeft
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val))

/-- この全切断は、元の companion 点を同じ end の反転比較へ送った点の uncurry。 -/
lemma circleCompanionBKReflectedSection_uncurry (z : Sp.{u} _⦋0⦌) :
    circleCompanionBKReflectedSection z =
      (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (circleCompanionBKEndPointMap z ≫
          circleCompanionBKReflection (nativeCotensorInput PointedSimplicialSet.circle z).val) := by
  rw [circleCompanionBKReflectedSection, circleCompanionBKEdgewiseSection,
    Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_postcomp]
  rfl

/-- uncurry に使った点は、既存の companion の反転 end の点に厳密一致する。 -/
lemma circleCompanionBKReflectedSection_point (z : Sp.{u} _⦋0⦌) :
    SSet.unitHomEquiv _ (circleCompanionBKEndPointMap z ≫
      circleCompanionBKReflection (nativeCotensorInput PointedSimplicialSet.circle z).val) =
        circleCompanionReflectedEndPoint z := by
  rw [PointedMapping.unitHomEquiv_post]
  rfl

/-- 元の reflected 全切断の各初区間から作る、実際の weighted 錐の三角形。 -/
def circleCompanionReflectedTriangle (z : Sp.{u} _⦋0⦌) (k : WalkingPair) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex
    (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val)
    (cotensor PointedSimplicialSet.circle
      (nativeCotensorInput PointedSimplicialSet.circle z).val)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight (LoopEdgewiseSection.arrow k) ≫
      Functor.whiskerLeft (LoopEdgewiseSection.arrow k) (circleCompanionBKReflectedSection z))

/-- 元の weighted 錐の三角形の trace は、元の解像三単体の左辺そのもの。 -/
lemma circleCompanionReflectedTriangle_trace (z : Sp.{u} _⦋0⦌) (k : WalkingPair) :
    CoherentPathCoordinates.triangleTrace (circleCompanionReflectedTriangle z k) =
      SSet.yonedaEquiv.symm (stdSimplex.edge 3 0 1 (by decide)) ≫
        circleCompanionEdgewiseTetrahedron z k := by
  unfold circleCompanionReflectedTriangle circleCompanionBKReflectedSection
  rw [CoherentPathCoordinates.weightedEdgewiseSection_triangleTrace,
    EdgewiseCoordinates.leftCurve]
  unfold circleCompanionEdgewiseTetrahedron LoopEdgewiseSection.parameter
  rw [circleCompanionBKEdgewiseLoopSection_central]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
