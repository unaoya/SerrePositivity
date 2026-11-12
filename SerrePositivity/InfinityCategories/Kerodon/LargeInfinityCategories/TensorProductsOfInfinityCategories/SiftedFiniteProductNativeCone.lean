module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiniteKanProductNative
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.F2PresentableSiftedFiniteFiberProduct
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpecifiedApexConeRestrictions
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackKanObjects
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.EdgeApexPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible

/-!
概要：元の有限共通 fiber 積の全空間 Kan 模型を頂点とする、native な全有限積錐。
方針：元の有限積比較の同じ coherent 辺で元の反復積の全錐を輸送する。
規約：同じ頂点辺と、全時刻で元の底図式を固定する全錐円柱を保持する。
使われ方：P_Σ の sifted 余極限閉性で使う全有限非空積の比較。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
variable (n : ℕ) {B : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] {E : Fin (n + 1) → SSet.{u}}
  (p : (i : Fin (n + 1)) → E i ⟶ B) (hp : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (p i))

/-- 元の有限積比較を、元の Kan 対象間の指定射に束ねる。 -/
def finiteTotalComparisonKanMap : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProduct n p) ⟶
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (E i)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductKanComparison n p

/-- 元の有限積比較の coherent な辺そのものを持つ頂点円柱。 -/
def finiteTotalComparisonApexPrism :
    (Δ[1] : SSet.{u + 1}) ⊗ (Δ[0] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (finiteTotalComparisonKanMap n p))

/-- 元の全空間の有限積比較による、頂点指定の全極限錐の輸送。 -/
def finiteSiftedProductNativeConeTransport : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.SpecifiedApexLimitConeTransport
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (E i)))
    (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProduct n p))))
    (finiteTotalComparisonApexPrism n p) := by
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n
      (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (E i))) :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct_kanComplex _ _ (fun _ ↦ inferInstance)
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.specifiedApexLimitConeTransport _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone_isLimit _ _) _ _
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism_zero _) (by
      unfold finiteTotalComparisonApexPrism
      rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism_one]
      apply SSet.yonedaEquiv.injective
      change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _ = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone n
        (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (E i))).vertex
      exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone_vertex _ _).symm)
    (fun x ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism_vertical_isInvertible _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProductKanComparison_homotopyEquivalence n p hp).isQCatEquivalence) x)

/-- 元の finite 共通 fiber 積の全空間 Kan 模型を頂点とする native な全有限積錐。 -/
def finiteSiftedProductNativeCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (E i)))) :=
  (finiteSiftedProductNativeConeTransport n p hp).cone

/-- 元の全空間 Kan 模型を頂点とする全錐は、実際の native な有限積錐。 -/
lemma finiteSiftedProductNativeCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (finiteSiftedProductNativeCone n p hp) :=
  (finiteSiftedProductNativeConeTransport n p hp).isLimit

/-- 輸送した native 全錐の頂点は、元の有限 fiber 積の全空間模型と厳密に一致。 -/
lemma finiteSiftedProductNativeCone_vertex : (finiteSiftedProductNativeCone n p hp).vertex =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.finiteCommonFiberProduct n p)) := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ (finiteSiftedProductNativeCone n p hp).val) = _
  dsimp only [finiteSiftedProductNativeCone]
  rw [(finiteSiftedProductNativeConeTransport n p hp).apex_eq, Equiv.apply_symm_apply]

/-- 元の反復積錐への、同じ比較辺を頂点辺とする全錐ホモトピー。 -/
def finiteSiftedProductNativeConeHomotopy : SSet.Homotopy (finiteSiftedProductNativeCone n p hp).val
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (E i))).val :=
  (finiteSiftedProductNativeConeTransport n p hp).homotopy

/-- 全錐円柱の頂点制限は元の有限積比較の同じ円柱。 -/
lemma finiteSiftedProductNativeConeHomotopy_apex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (finiteSiftedProductNativeConeHomotopy n p hp).h =
      (β_ (Δ[0] : SSet.{u + 1}) (Δ[1] : SSet.{u + 1})).hom ≫
        finiteTotalComparisonApexPrism n p :=
  (finiteSiftedProductNativeConeTransport n p hp).apex

/-- 全錐円柱の底制限は全時刻で元の全空間の図式そのもの。 -/
lemma finiteSiftedProductNativeConeHomotopy_diagram :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (finiteSiftedProductNativeConeHomotopy n p hp).h =
      fst _ (Δ[1] : SSet.{u + 1}) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (E i))) :=
  (finiteSiftedProductNativeConeTransport n p hp).diagram

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
