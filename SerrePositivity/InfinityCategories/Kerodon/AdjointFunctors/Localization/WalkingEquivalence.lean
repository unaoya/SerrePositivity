module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoreAnodyneLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement

/-!
概要：標準区間の実 Kan 置換を、可逆辺を自由に延長する区間として構成する。
方針：元の anodyne 包含を保持し、core の Kan 充填で指定された底を固定して延長する。
規約：関手圏での普遍性は後続で証明。使われ方：一般商の辺反転の貼合せ。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

def walkingEquivalence : SSet.{u} :=
  SimplicialModel.AnodyneKanReplacement.functor.obj (Δ[1] : SSet.{u})

def walkingEquivalenceEdge : (Δ[1] : SSet.{u}) ⟶ walkingEquivalence :=
  SimplicialModel.AnodyneKanReplacement.unit.app _

lemma walkingEquivalenceEdge_anodyne : anodyneExtensions walkingEquivalenceEdge.{u} :=
  SimplicialModel.AnodyneKanReplacement.unit_anodyne _

instance walkingEquivalence_kanComplex : KanComplex walkingEquivalence.{u} :=
  (fibration_iff _).mpr (SimplicialModel.AnodyneKanReplacement.terminal_rlp _)

/-- 可逆な元の辺そのものを core の区間に持ち上げる。 -/
def invertibleIntervalCoreLift {X : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ X)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv e))) :
    (Δ[1] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u}) :=
  SSet.yonedaEquiv.symm ⟨SSet.yonedaEquiv e, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_edge_iff _).mpr he⟩

lemma invertibleIntervalCoreLift_ι {X : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ X)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv e))) :
    invertibleIntervalCoreLift e he ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι = e := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  unfold invertibleIntervalCoreLift
  rw [Equiv.apply_symm_apply]
  rfl

lemma invertibleInterval_allEdges {X : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ X)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv e))) (s : Δ[1] _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (e.app (Opposite.op ⦋1⦌) s)) := by
  rw [← invertibleIntervalCoreLift_ι e he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge ((invertibleIntervalCoreLift e he).app _ s)

/-- 指定された底の全可逆区間を保ち、元の可逆辺を相対的に延長する。 -/
lemma walkingEquivalence_relative_extension {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (e : (Δ[1] : SSet.{u}) ⟶ X)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv e)))
    (g : walkingEquivalence.{u} ⟶ Y) (h : e ≫ p = walkingEquivalenceEdge ≫ g) :
    ∃ l : walkingEquivalence.{u} ⟶ X, walkingEquivalenceEdge ≫ l = e ∧ l ≫ p = g :=
  exists_coreAnodyne_lift p hp walkingEquivalenceEdge walkingEquivalenceEdge_anodyne e g
    (invertibleInterval_allEdges e he) (kanSource_map_invertible g) h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
