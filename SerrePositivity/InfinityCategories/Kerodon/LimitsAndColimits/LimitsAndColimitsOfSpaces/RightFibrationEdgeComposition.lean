module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationEdgeTriangle
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.IntervalConstantFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedComposition

/-!
概要：共通 span の端点射 β_native が、全族で標準後合成を表すこと。
方針：同じ実三角形の三面から h Fun の合成則を得て、区間族の忠実性を使う。
規約：辺形状のみ。使われ方：G8 の固定端点模型への移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open MorphismSpaces IsomorphismsAndIsofibrations LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：指定辺の始点への制限は、その頂点の Yoneda 射。
方針：Yoneda の面の公式と辺の始点条件を使う。
規約：辺の実代表を保持。使われ方：辺形状の共通 span の入力。 -/
lemma edgeYoneda_first {E : SSet.{u}} {c d : E _⦋0⦌} (e : E.Edge c d) :
    stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge =
      SSet.yonedaEquiv.symm c := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  simpa only [Equiv.apply_symm_apply] using e.src_eq

/-- 概要：指定辺の終点への制限は、その頂点の Yoneda 射。
方針：Yoneda の面の公式と辺の終点条件を使う。
規約：辺の実代表を保持。使われ方：同じ共通 span の端点射。 -/
lemma edgeYoneda_last {E : SSet.{u}} {c d : E _⦋0⦌} (e : E.Edge c d) :
    stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge =
      SSet.yonedaEquiv.symm d := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  simpa only [Equiv.apply_symm_apply] using e.tgt_eq

variable {E B : SSet.{u}} [Quasicategory B] (r : E ⟶ B) [RightFibration r]
  {c d : E _⦋0⦌} (e : E.Edge c d) (x : B _⦋0⦌)

/-- 概要：元の辺上の同じ共通切断から得る端点写像。
方針：既存の β_native を辺の実代表へ適用する。
規約：別の切断を選ばない。使われ方：標準後合成との比較。 -/
def rightFibrationEdgeNative : Basic.pinchedHom x (r.app _ c) ⟶
    Basic.pinchedHom x (r.app _ d) :=
  rightFibrationInitialDiagramEndpointMap r (SSet.yonedaEquiv.symm e.edge)
    (stdSimplex.δ (1 : Fin 2)) edgeInitialVertex_leftAnodyne c (edgeYoneda_first e) x
    (stdSimplex.δ (0 : Fin 2)) d (edgeYoneda_last e)

/-- 概要：β_native の区間像の全族は、元の区間族と指定辺との合成を表す。
方針：同じ実三角形の三面を既存の合成構造へ渡す。
規約：全パラメータ pinched Hom を保持。使われ方：標準後合成との同定。 -/
lemma rightFibrationEdgeNative_family :
    intervalFamilyHom (pinchedHomToIntervalMappingSpace x (r.app _ c)) ≫
        constantFunctorHomMap _ (SSet.Truncated.HomotopyCategory.homMk (e.map r)) =
      intervalFamilyHom (rightFibrationEdgeNative r e x ≫
        pinchedHomToIntervalMappingSpace x (r.app _ d)) := by
  rw [← intervalFamilyHom_const_edge]
  apply intervalTriangleFamily_hom_comp _ _ _
    (rightFibrationEdgeTriangle r (SSet.yonedaEquiv.symm e.edge) c (edgeYoneda_first e) x)
  · exact rightFibrationEdgeTriangle_first r _ c _ x
  · rw [rightFibrationEdgeTriangle_edge, intervalFamilyHomotopy_const_edge]
    rw [SSet.Edge.map_edge, SSet.yonedaEquiv_symm_comp]
  · exact rightFibrationEdgeTriangle_long r _ c _ x d (edgeYoneda_last e)

/-- 概要：β_native の区間像は、標準後合成の同じ全族とホモトピック。
方針：全族の合成則と既存の区間後合成の仕様を照合し、族の忠実性を使う。
規約：必要な同型を仮定しない。使われ方：固定端点模型への全族移送。 -/
lemma rightFibrationEdgeNative_interval_homotopy :
    Nonempty (SSet.Homotopy
      (rightFibrationEdgeNative r e x ≫ pinchedHomToIntervalMappingSpace x (r.app _ d))
      (pinchedHomToIntervalMappingSpace x (r.app _ c) ≫ intervalPostcompose x
        (SSet.Truncated.HomotopyCategory.homMk (e.map r)))) := by
  apply intervalFamilyHom_eq_imp_homotopy
  rw [intervalPostcompose_family, rightFibrationEdgeNative_family]

/-- 概要：同じ β_native は、元の pinched 模型の標準後合成に同型。
方針：区間族のホモトピーを可逆二胞体にして、指定比較の逆で戻す。
規約：元の比較と選んだ切断を保持。使われ方：錐の辺との全族比較。 -/
def rightFibrationEdgeNative_postcomposeIso :
    FunctorIso (rightFibrationEdgeNative r e x)
      (postcompose x (SSet.Truncated.HomotopyCategory.homMk (e.map r))) := by
  let q := (pinchedHomToIntervalMappingSpace_isQCatEquivalence x (r.app _ d)).choose
  have h := functorIsoOfSimplicialHomotopy
    (rightFibrationEdgeNative_interval_homotopy r e x).some
  have hi : FunctorIso (rightFibrationEdgeNative r e x)
      (rightFibrationEdgeNative r e x ≫ q.hom ≫ q.inv) := by
    simpa only [Category.assoc, Category.comp_id] using
      (FunctorIso.precomp q.homInvIso (rightFibrationEdgeNative r e x)).symm
  have ho : FunctorIso (rightFibrationEdgeNative r e x ≫ q.hom ≫ q.inv)
      (postcompose x (SSet.Truncated.HomotopyCategory.homMk (e.map r))) := by
    simpa only [q, IsQCatEquivalence.choose, postcompose, liftMap, Category.assoc] using
      FunctorIso.postcomp h q.inv
  exact hi ≪≫ ho

/-- 概要：元の right fibration の Hom 比較は、指定辺の標準後合成と全族で可換。
方針：共通 span の端点比較と、同じ β_native の標準後合成との同型を合成する。
規約：必要な全族同型を仮定しない。使われ方：G8 の錐の辺の比較。 -/
def rightFibrationHomComparison_edgeIso :
    FunctorIso (rightFibrationHomComparison r c x)
      (postcompose x (SSet.Truncated.HomotopyCategory.homMk (e.map r)) ≫
        rightFibrationHomComparison r d x) :=
  rightFibrationInitialDiagramEndpointIso r (SSet.yonedaEquiv.symm e.edge)
    (stdSimplex.δ (1 : Fin 2)) edgeInitialVertex_leftAnodyne c (edgeYoneda_first e) x
    (stdSimplex.δ (0 : Fin 2)) d (edgeYoneda_last e) ≪≫
      FunctorIso.postcomp (rightFibrationEdgeNative_postcomposeIso r e x)
        (rightFibrationHomComparison r d x)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
