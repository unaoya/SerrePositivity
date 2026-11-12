module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalKanCoordinates
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberwiseIntervalEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.KanEquivalencePaths
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathLifting
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead

/-!
概要：両端を固定して選んだ定値底の Kan path 比較は実際のホモトピー同値。
方針：始点評価の厳密な可換式と、両方の始点評価の弱同値性で比較を消去する。
規約：底や全空間の充填性・filtered 性は不要。
使われ方：一般 coherent な cospan の引き戻し比較の path 成分。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：Kan 複体の区間関手の始点評価は弱ホモトピー同値。
方針：全 path が可逆である同型を介して、自明 Kan な可逆 path の始点評価へ移す。
規約：元の始点評価そのもの。使われ方：指定両端の Kan path 比較の消去。 -/
lemma intervalEndpoint_zero_isWeakHomotopyEquivalence (X : SSet.{u}) [KanComplex X] :
    IsWeakHomotopyEquivalence ((intervalEndpointNatTrans 0).app X) := by
  have h : equivalencePathι X ≫ (intervalEndpointNatTrans 0).app X =
      equivalencePathEndpoint X 0 := rfl
  apply (isPrecompositionEquivalence_of_iso
    (asIso (equivalencePathι X))).isWeakHomotopyEquivalence.cancel_left
  rw [asIso_hom, h]
  change IsWeakHomotopyEquivalence (equivalencePathEndpoint X 0)
  exact (isQCatEquivalence_of_trivialKanFibration
    (equivalencePathEndpoint X 0)).isWeakHomotopyEquivalence

/-- 概要：両端固定の Kan path 比較は弱ホモトピー同値。
方針：始点での可換式を使い、元の始点評価と標的の始点評価の弱同値性を合成する。
規約：選んだ比較射を変更しない。使われ方：指定 path を保つ引き戻し比較の一因子。 -/
lemma fiberwiseIntervalKanComparison_isWeakHomotopyEquivalence {E B : SSet.{u}} (p : E ⟶ B) :
    IsWeakHomotopyEquivalence (fiberwiseIntervalKanComparison p) := by
  have h := continuousKanReplacement_map_isWeakHomotopyEquivalence _
    (fiberwiseIntervalEndpoint_zero_isWeakHomotopyEquivalence p)
  rw [← fiberwiseIntervalKanComparison_endpoint p 0] at h
  exact (intervalEndpoint_zero_isWeakHomotopyEquivalence
    (continuousKanReplacement.obj E)).cancel_right h

/-- 概要：元の二つの評価を保持する Kan path 比較は単体的ホモトピー逆を持つ。
方針：両 Kan 模型間の弱同値性を実際のホモトピー逆に移す。
規約：元の単位・両端の厳密な一致を保持。使われ方：native な path 比較の同値。 -/
lemma fiberwiseIntervalKanComparison_homotopyEquivalence {E B : SSet.{u}} (p : E ⟶ B) :
    IsSimplicialHomotopyEquivalence (fiberwiseIntervalKanComparison p) :=
  (fiberwiseIntervalKanComparison_isWeakHomotopyEquivalence p).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
