module
public import SerrePositivity.KST.SConstruction.TerminalPathSpace
public import SerrePositivity.KST.Spectra.EndpointCircle

/-! # 終点基点の二端点商と元の円
概要：終点を基点にした区間の始点包含の cofiber は既存の円そのものと同型。
方針：二つの端点を表す余積を交換し、元の商射を保つ互逆の降下を作る。
規約：区間の向きを変えない。使われ方：終点固定 path の fiber と元の loop の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet

/-- 二つの端点の交換で元の始点基点の端点包含を回収する。 -/
lemma terminalIntervalStart_swap :
    (coprod.braiding (𝟙_ SSet.{u}) (𝟙_ SSet.{u})).hom ≫ terminalIntervalStart.{u}.right =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right := by
  apply coprod.hom_ext <;>
    simp [terminalIntervalStart_right, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint_right, coprod.braiding]

/-- 終点を基点にした区間のもう一方の端点も潰した商。 -/
abbrev terminalEndpointCircle : PointedSimplicialSet.{u} :=
  PointedObject.cofiber terminalIntervalStart.{u}.right

/-- 終点基点の端点商から既存の始点基点の端点商への射。 -/
def terminalEndpointCircleToEndpointCircle : terminalEndpointCircle.{u} ⟶
    Spectra.endpointCircle.{u} :=
  PointedObject.cofiberDesc terminalIntervalStart.{u}.right Spectra.endpointCircle.{u}
    (PointedObject.cofiberQuotient _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right) (by
      rw [terminalIntervalStart_right, Category.assoc,
        PointedObject.cofiberQuotient_condition, comp_toUnit_assoc])

/-- 既存の端点商から終点基点の端点商への逆向きの射。 -/
def endpointCircleToTerminalEndpointCircle : Spectra.endpointCircle.{u} ⟶
    terminalEndpointCircle.{u} :=
  PointedObject.cofiberDesc _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right terminalEndpointCircle.{u}
    (PointedObject.cofiberQuotient terminalIntervalStart.{u}.right) (by
      rw [← terminalIntervalStart_swap, Category.assoc,
        PointedObject.cofiberQuotient_condition, comp_toUnit_assoc])

/-- 二端点の表示の交換は元の区間からの商射を保つ点つき同型。 -/
def terminalEndpointCircleSwapIso : terminalEndpointCircle.{u} ≅ Spectra.endpointCircle.{u} where
  hom := terminalEndpointCircleToEndpointCircle.{u}
  inv := endpointCircleToTerminalEndpointCircle.{u}
  hom_inv_id := by
    apply PointedObject.cofiber_hom_ext terminalIntervalStart.{u}.right
    simp [terminalEndpointCircleToEndpointCircle, endpointCircleToTerminalEndpointCircle,
      Under.comp_right]
  inv_hom_id := by
    apply PointedObject.cofiber_hom_ext _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right
    simp [terminalEndpointCircleToEndpointCircle, endpointCircleToTerminalEndpointCircle,
      Under.comp_right]

/-- 終点基点の端点商と既存の円の、元の区間の向きを保つ同型。 -/
def terminalEndpointCircleIso : terminalEndpointCircle.{u} ≅ PointedSimplicialSet.circle.{u} :=
  terminalEndpointCircleSwapIso.{u} ≪≫ Spectra.endpointCircleIso.{u}

/-- 新しい円の表示の同型は元の区間からの商射と厳密に可換。 -/
lemma terminalEndpointCircleIso_quotient :
    PointedObject.cofiberQuotient terminalIntervalStart.{u}.right ≫
      terminalEndpointCircleIso.hom.right =
        PointedObject.cofiberQuotient (boundary.{u} 1).ι := by
  change PointedObject.cofiberQuotient terminalIntervalStart.{u}.right ≫
    (terminalEndpointCircleToEndpointCircle.{u}.right ≫
      Spectra.endpointCircleToCircle.{u}.right) = _
  rw [← Category.assoc, terminalEndpointCircleToEndpointCircle,
    PointedObject.cofiberQuotient_desc, Spectra.endpointCircleToCircle,
    PointedObject.cofiberQuotient_desc]

end SerrePositivity.KST.SConstruction
