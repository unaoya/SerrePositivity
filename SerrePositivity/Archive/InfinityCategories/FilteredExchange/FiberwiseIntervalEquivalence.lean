module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberwiseIntervalContraction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopyInverse
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakFunctoriality

/-!
概要：定値底の path の始点評価は底上の実際のホモトピー逆を持つ。
方針：定値 path の切断と底を固定する形状収縮を使う。
規約：底や全空間の充填性は不要。
使われ方：全空間 Kan path 比較の始点での弱同値判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：始点で定値な path から元の path への底上のホモトピー。
方針：形状収縮の両端と空な相対条件を使う。
規約：底射の全時刻での一致は fiberwiseIntervalContraction_projection。 -/
def fiberwiseIntervalContractionHomotopy {E B : SSet.{u}} (p : E ⟶ B) :
    SSet.Homotopy (fiberwiseIntervalEndpoint p 0 ≫ fiberwiseFunctorConstant p Δ[1])
      (𝟙 (fiberwiseFunctorSpace p (Δ[1] : SSet.{u}))) where
  h := fiberwiseIntervalContraction p
  h₀ := fiberwiseIntervalContraction_zero p
  h₁ := fiberwiseIntervalContraction_one p
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：始点評価は元の定値 path を逆とする単体的ホモトピー同値。
方針：底上の収縮と切断の厳密な片逆の式を合わせる。
規約：充填性の仮定は不要。使われ方：Kan 模型に移す前の弱同値。 -/
lemma fiberwiseIntervalEndpoint_zero_homotopyEquivalence {E B : SSet.{u}} (p : E ⟶ B) :
    IsSimplicialHomotopyEquivalence (fiberwiseIntervalEndpoint p 0) := by
  refine ⟨fiberwiseFunctorConstant p Δ[1], ⟨fiberwiseIntervalContractionHomotopy p⟩, ?_⟩
  rw [fiberwiseFunctorConstant_endpoint]
  exact ⟨functorHomotopyRefl (𝟙 E)⟩

/-- 概要：底を固定した path の始点評価は弱ホモトピー同値。
方針：実際のホモトピー逆を Kan 標的への前合成へ移す。
規約：底の filtered 性も不要。使われ方：Kan path 比較の二辺の消去。 -/
lemma fiberwiseIntervalEndpoint_zero_isWeakHomotopyEquivalence {E B : SSet.{u}}
    (p : E ⟶ B) : IsWeakHomotopyEquivalence (fiberwiseIntervalEndpoint p 0) :=
  (fiberwiseIntervalEndpoint_zero_homotopyEquivalence p).isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
