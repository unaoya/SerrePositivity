module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteKanProductNative
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteCoherentProductKanComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpecifiedApexConeRestrictions
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwisePullbackKanObjects
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.EdgeApexPrism
public import SerrePositivity.InfinityCategories.F1.CoherentKanInvertible

/-!
概要：元の有限 coherent 積図式の余極限 Kan 模型を頂点とする、native な全有限積錐。
方針：元の有限 coherent 積比較の同じ辺で元の反復積の全錐を輸送する。
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
variable (n : ℕ) {B : SSet.{u}} [IsSiftedInfinity B]
  (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))

/-- 元の有限積比較を、元の Kan 対象間の指定射に束ねる。 -/
def finiteCoherentTotalComparisonKanMap :
    F2.coherentDiagramTotalKanObject (finiteCoherentSpaceProduct n F) ⟶
    finiteKanProductObject n (fun i ↦ F2.coherentDiagramTotalKanObject (F i)) :=
  finiteCoherentProductTotalKanComparison n F

/-- 元の有限積比較の coherent な辺そのものを持つ頂点円柱。 -/
def finiteCoherentTotalComparisonApexPrism :
    (Δ[1] : SSet.{u + 1}) ⊗ (Δ[0] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} :=
  F2.edgeApexPrism (coherentNerveEdge (finiteCoherentTotalComparisonKanMap n F))

/-- 元の全空間の有限積比較による、頂点指定の全極限錐の輸送。 -/
def finiteSiftedCoherentProductNativeConeTransport : F2.SpecifiedApexLimitConeTransport
    (finiteKanProductNativeCone n (fun i ↦ F2.coherentDiagramTotalKanObject (F i)))
    (SSet.yonedaEquiv.symm
      (coherentNerveVertex (F2.coherentDiagramTotalKanObject (finiteCoherentSpaceProduct n F))))
    (finiteCoherentTotalComparisonApexPrism n F) := by
  have : KanComplex (nonemptyFiniteSSetProduct n
      (fun i ↦ F2.coherentDiagramTotalKan (F i))) :=
    nonemptyFiniteSSetProduct_kanComplex _ _ (fun _ ↦ inferInstance)
  exact F2.specifiedApexLimitConeTransport _ (finiteKanProductNativeCone_isLimit _ _) _ _
    (F2.edgeApexPrism_zero _) (by
      unfold finiteCoherentTotalComparisonApexPrism
      rw [F2.edgeApexPrism_one]
      apply SSet.yonedaEquiv.injective
      change coherentNerveVertex _ = (finiteKanProductNativeCone n
        (fun i ↦ F2.coherentDiagramTotalKanObject (F i))).vertex
      exact (finiteKanProductNativeCone_vertex _ _).symm)
    (fun x ↦ F2.edgeApexPrism_vertical_isInvertible _
      (coherentKanEdge_isInvertible_of_isQCatEquivalence
        (finiteCoherentProductTotalKanComparison_homotopyEquivalence n F).isQCatEquivalence) x)

/-- 元の有限 coherent 積図式の余極限 Kan 模型を頂点とする native な全有限積錐。 -/
def finiteSiftedCoherentProductNativeCone : JoinCone (kanDiagramCoherentNerve
    (finiteKanProductDiagram n (fun i ↦ F2.coherentDiagramTotalKanObject (F i)))) :=
  (finiteSiftedCoherentProductNativeConeTransport n F).cone

/-- 元の全空間 Kan 模型を頂点とする全錐は、実際の native な有限積錐。 -/
lemma finiteSiftedCoherentProductNativeCone_isLimit :
    IsLimitCone (finiteSiftedCoherentProductNativeCone n F) :=
  (finiteSiftedCoherentProductNativeConeTransport n F).isLimit

/-- 輸送した native 全錐の頂点は、元の有限 coherent 積図式の余極限模型と厳密に一致。 -/
lemma finiteSiftedCoherentProductNativeCone_vertex :
    (finiteSiftedCoherentProductNativeCone n F).vertex =
    coherentNerveVertex (F2.coherentDiagramTotalKanObject (finiteCoherentSpaceProduct n F)) := by
  change SSet.yonedaEquiv (joinInl _ _ ≫ (finiteSiftedCoherentProductNativeCone n F).val) = _
  dsimp only [finiteSiftedCoherentProductNativeCone]
  rw [(finiteSiftedCoherentProductNativeConeTransport n F).apex_eq, Equiv.apply_symm_apply]

/-- 元の反復積錐への、同じ比較辺を頂点辺とする全錐ホモトピー。 -/
def finiteSiftedCoherentProductNativeConeHomotopy :
    SSet.Homotopy (finiteSiftedCoherentProductNativeCone n F).val
    (finiteKanProductNativeCone n (fun i ↦ F2.coherentDiagramTotalKanObject (F i))).val :=
  (finiteSiftedCoherentProductNativeConeTransport n F).homotopy

/-- 全錐円柱の頂点制限は元の有限積比較の同じ円柱。 -/
lemma finiteSiftedCoherentProductNativeConeHomotopy_apex :
    (joinInl _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (finiteSiftedCoherentProductNativeConeHomotopy n F).h =
      (β_ (Δ[0] : SSet.{u + 1}) (Δ[1] : SSet.{u + 1})).hom ≫
        finiteCoherentTotalComparisonApexPrism n F :=
  (finiteSiftedCoherentProductNativeConeTransport n F).apex

/-- 全錐円柱の底制限は全時刻で元の全空間の図式そのもの。 -/
lemma finiteSiftedCoherentProductNativeConeHomotopy_diagram :
    (joinInr _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (finiteSiftedCoherentProductNativeConeHomotopy n F).h =
      fst _ (Δ[1] : SSet.{u + 1}) ≫
        kanDiagramCoherentNerve
          (finiteKanProductDiagram n (fun i ↦ F2.coherentDiagramTotalKanObject (F i))) :=
  (finiteSiftedCoherentProductNativeConeTransport n F).diagram

end SerrePositivity.InfinityCategories.HomotopyLimits
