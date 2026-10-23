module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CospanFiniteKanPointTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CospanTransportedKanPointReflection

/-!
概要：元の二入力から来る有限 Kan 引き戻し射を、元の一値の引き戻しで検出する。
方針：有限 path 模型の輸送と、端点固定の値への反映を実際の引き戻し内で合成する。
規約：終点は値の包含・単位・元の Kan 比較による実際の像。
使われ方：一般 coherent filtered 引き戻し比較の標的側の有限持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の有限二入力と指定 Kan path は、元の一値の実際の引き戻し比較像で検出できる。
方針：二段の全境界正方形の輸送と端点固定反映を構成済み比較へ接続する。
規約：strict 図式への置換を要求しない。使われ方：標的側の有限持ち上げの元の入力の場合。 -/
lemma fiberwisePullbackKanComparison_original_input_detection {K E D H B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] (u : K ⟶ E) (v : K ⟶ D)
    (H₀ : SSet.Homotopy (u ≫ f ≫ continuousKanReplacementUnit.app H)
      (v ≫ g ≫ continuousKanReplacementUnit.app H)) :
    ∃ b : B _⦋0⦌, ∃ a : K ⟶ intervalPullback (vertexFiberMap (f ≫ p) p f rfl b)
      (vertexFiberMap (g ≫ p) p g rfl b),
      Nonempty (SSet.Homotopy (kanCospanPoint f g u v H₀)
        (a ≫ fiberwisePullbackValueKanComparison p f g b)) := by
  obtain ⟨b, s, t, M, m, z, w, hz, hw, H₁, h₁, ⟨J⟩⟩ :=
    cospan_finite_kan_point_transport p f g u v H₀
  obtain ⟨L, ⟨T⟩⟩ := cospanTransportedKanPoint_reflection p f g b s t m z w hz hw H₁ h₁
  refine ⟨b, intervalPullbackHomotopyPoint (vertexFiberMap (f ≫ p) p f rfl b)
    (vertexFiberMap (g ≫ p) p g rfl b) s t L, ?_⟩
  apply (functorVertex_piZero_eq_iff_homotopy _ _).1
  exact ((functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨J⟩).trans
    ((functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨T⟩)

end SerrePositivity.InfinityCategories.F2
