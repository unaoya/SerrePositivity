module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanSpecifiedIntervalLift
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeEquivalencePathExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

/-!
概要：指定区間 path の持ち上げは、入力端点から出力端点への指定関手同型を与える。
方針：同じ持ち上げの可逆 path の同型を、入力端点の厳密な式で輸送する。
規約：元の持ち上げを使用。使われ方：切断 cospan の厳密化後の成分の同値性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B T : SSet.{u}} [KanComplex E] [KanComplex B]
  (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
  (a : T ⟶ E) (h : T ⟶ (ihom (Δ[1] : SSet.{u})).obj B)
  (ha : h ≫ (intervalEndpointNatTrans 0).app B = a ≫ p)

/-- 元の入力から、同じ指定持ち上げの終点への具体的な関手同型。 -/
def kanSpecifiedIntervalLiftEndpointIso :
    FunctorIso a (kanSpecifiedIntervalLift p 0 a h ha ≫ equivalencePathEndpoint E 1) :=
  functorIsoOfEq (F1B.kanEquivalencePath_functorIso (kanSpecifiedIntervalLift p 0 a h ha))
    (kanSpecifiedIntervalLift_endpoint p 0 a h ha) rfl

/-- 入力が同値なら、指定 path に沿って移した同じ終点も単体的ホモトピー同値。 -/
lemma kanSpecifiedIntervalLiftEndpoint_homotopyEquivalence [KanComplex T]
    (he : IsSimplicialHomotopyEquivalence a) :
    IsSimplicialHomotopyEquivalence
      (kanSpecifiedIntervalLift p 0 a h ha ≫ equivalencePathEndpoint E 1) :=
  (he.isQCatEquivalence.ofFunctorIso
    (kanSpecifiedIntervalLiftEndpointIso p a h ha)).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
