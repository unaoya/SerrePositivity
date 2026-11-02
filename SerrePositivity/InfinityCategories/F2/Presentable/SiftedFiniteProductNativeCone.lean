module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteKanProductNative
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedFiniteFiberProduct
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.SpecifiedApexConeRestrictions
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackKanObjects
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.EdgeApexPrism
public import SerrePositivity.InfinityCategories.F1.Coherent.KanInvertible

/-!
概要：元の有限共通 fiber 積の全空間 Kan 模型を頂点とする、native な全有限積錐。
方針：元の有限積比較の同じ coherent 辺で元の反復積の全錐を輸送する。
規約：同じ頂点辺と、全時刻で元の底図式を固定する全錐円柱を保持する。
使われ方：P_Σ の sifted 余極限閉性で使う全有限非空積の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable (n : ℕ) {B : SSet.{u}} [IsSiftedInfinity B] {E : Fin (n + 1) → SSet.{u}}
  (p : (i : Fin (n + 1)) → E i ⟶ B) (hp : ∀ i, LeftFibration (p i))

/-- 元の有限積比較を、元の Kan 対象間の指定射に束ねる。 -/
def finiteTotalComparisonKanMap : F2.continuousKanObject (finiteCommonFiberProduct n p) ⟶
    finiteKanProductObject n (fun i ↦ F2.continuousKanObject (E i)) :=
  finiteCommonFiberProductKanComparison n p

/-- 元の有限積比較の coherent な辺そのものを持つ頂点円柱。 -/
def finiteTotalComparisonApexPrism :
    (Δ[1] : SSet.{u + 1}) ⊗ (Δ[0] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} :=
  F2.edgeApexPrism (coherentNerveEdge (finiteTotalComparisonKanMap n p))

/-- 元の全空間の有限積比較による、頂点指定の全極限錐の輸送。 -/
def finiteSiftedProductNativeConeTransport : F2.SpecifiedApexLimitConeTransport
    (finiteKanProductNativeCone n (fun i ↦ F2.continuousKanObject (E i)))
    (SSet.yonedaEquiv.symm
      (coherentNerveVertex (F2.continuousKanObject (finiteCommonFiberProduct n p))))
    (finiteTotalComparisonApexPrism n p) := by
  have : KanComplex (nonemptyFiniteSSetProduct n
      (fun i ↦ F2.continuousKanReplacement.obj (E i))) :=
    nonemptyFiniteSSetProduct_kanComplex _ _ (fun _ ↦ inferInstance)
  exact F2.specifiedApexLimitConeTransport _ (finiteKanProductNativeCone_isLimit _ _) _ _
    (F2.edgeApexPrism_zero _) (by
      unfold finiteTotalComparisonApexPrism
      rw [F2.edgeApexPrism_one]
      apply SSet.yonedaEquiv.injective
      change coherentNerveVertex _ = (finiteKanProductNativeCone n
        (fun i ↦ F2.continuousKanObject (E i))).vertex
      exact (finiteKanProductNativeCone_vertex _ _).symm)
    (fun x ↦ F2.edgeApexPrism_vertical_isInvertible _
      (coherentKanEdge_isInvertible_of_isQCatEquivalence
        (finiteCommonFiberProductKanComparison_homotopyEquivalence n p hp).isQCatEquivalence) x)

/-- 元の finite 共通 fiber 積の全空間 Kan 模型を頂点とする native な全有限積錐。 -/
def finiteSiftedProductNativeCone : JoinCone (kanDiagramCoherentNerve
    (finiteKanProductDiagram n (fun i ↦ F2.continuousKanObject (E i)))) :=
  (finiteSiftedProductNativeConeTransport n p hp).cone

/-- 元の全空間 Kan 模型を頂点とする全錐は、実際の native な有限積錐。 -/
lemma finiteSiftedProductNativeCone_isLimit : IsLimitCone (finiteSiftedProductNativeCone n p hp) :=
  (finiteSiftedProductNativeConeTransport n p hp).isLimit

/-- 輸送した native 全錐の頂点は、元の有限 fiber 積の全空間模型と厳密に一致。 -/
lemma finiteSiftedProductNativeCone_vertex : (finiteSiftedProductNativeCone n p hp).vertex =
    coherentNerveVertex (F2.continuousKanObject (finiteCommonFiberProduct n p)) := by
  change SSet.yonedaEquiv (joinInl _ _ ≫ (finiteSiftedProductNativeCone n p hp).val) = _
  dsimp only [finiteSiftedProductNativeCone]
  rw [(finiteSiftedProductNativeConeTransport n p hp).apex_eq, Equiv.apply_symm_apply]

/-- 元の反復積錐への、同じ比較辺を頂点辺とする全錐ホモトピー。 -/
def finiteSiftedProductNativeConeHomotopy : SSet.Homotopy (finiteSiftedProductNativeCone n p hp).val
    (finiteKanProductNativeCone n (fun i ↦ F2.continuousKanObject (E i))).val :=
  (finiteSiftedProductNativeConeTransport n p hp).homotopy

/-- 全錐円柱の頂点制限は元の有限積比較の同じ円柱。 -/
lemma finiteSiftedProductNativeConeHomotopy_apex :
    (joinInl _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (finiteSiftedProductNativeConeHomotopy n p hp).h =
      (β_ (Δ[0] : SSet.{u + 1}) (Δ[1] : SSet.{u + 1})).hom ≫
        finiteTotalComparisonApexPrism n p :=
  (finiteSiftedProductNativeConeTransport n p hp).apex

/-- 全錐円柱の底制限は全時刻で元の全空間の図式そのもの。 -/
lemma finiteSiftedProductNativeConeHomotopy_diagram :
    (joinInr _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (finiteSiftedProductNativeConeHomotopy n p hp).h =
      fst _ (Δ[1] : SSet.{u + 1}) ≫
        kanDiagramCoherentNerve
          (finiteKanProductDiagram n (fun i ↦ F2.continuousKanObject (E i))) :=
  (finiteSiftedProductNativeConeTransport n p hp).diagram

end SerrePositivity.InfinityCategories.HomotopyLimits
