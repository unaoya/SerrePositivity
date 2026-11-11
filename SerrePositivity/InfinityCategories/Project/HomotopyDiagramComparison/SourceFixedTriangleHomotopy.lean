module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalArrowComparison
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：指定した三角形を始点固定の正方形へ引き戻し、同じ二辺の円柱を構成する。
方針：既存の比較形状の終端辺・右退化との合成を計算する。
規約：三角形や円柱を選び直さない。使われ方：右修正面から共通長辺の円柱への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 比較正方形の終点の辺は、元の三角形の終端辺そのもの。 -/
lemma sourceFixedTriangleShape_target :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableTriangleComparisonShape =
      stdSimplex.δ (0 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 右退化を比較正方形へ引き戻すと、時間に依存しない元の辺になる。 -/
lemma sourceFixedTriangleShape_base :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableTriangleComparisonShape.{u} ≫ stdSimplex.σ (1 : Fin 2) =
      fst (Δ[1] : SSet.{u}) Δ[1] := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  rintro ⟨p, q⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
  fin_cases i <;> fin_cases j <;> decide

/-- 正方形の始点は、三角形の元の初期頂点で全時刻に固定される。 -/
lemma sourceFixedTriangleShape_initial :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableTriangleComparisonShape =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫
        (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  rintro ⟨p, q⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
  fin_cases i <;> fin_cases j <;> decide

variable {E B : SSet.{u}} (τ : (Δ[2] : SSet.{u}) ⟶ E)

/-- 同じ指定三角形の初辺から長辺へ向かう、始点固定の実際の円柱。 -/
def sourceFixedTriangleHomotopy :
    SSet.Homotopy (stdSimplex.δ (2 : Fin 3) ≫ τ) (stdSimplex.δ (1 : Fin 3) ≫ τ) where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableTriangleComparisonShape ≫ τ
  h₀ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableTriangleComparisonShape ≫ τ) = _
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun z ↦ z ≫ τ) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableTriangleComparisonShape_bottom)
  h₁ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableTriangleComparisonShape ≫ τ) = _
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun z ↦ z ≫ τ) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableTriangleComparisonShape_top)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 円柱は、元の指定三角形を同じ比較正方形で引き戻した raw な射である。 -/
lemma sourceFixedTriangleHomotopy_raw :
    (sourceFixedTriangleHomotopy τ).h = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableTriangleComparisonShape ≫ τ := rfl

/-- 円柱の終点制限は元の終端辺を厳密に回収する。 -/
lemma sourceFixedTriangleHomotopy_target :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ (sourceFixedTriangleHomotopy τ).h =
      stdSimplex.δ (0 : Fin 3) ≫ τ :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun z ↦ z ≫ τ) sourceFixedTriangleShape_target)

/-- 元の三角形が右退化を被覆すれば、円柱は元の底の辺を全時刻で固定する。 -/
lemma sourceFixedTriangleHomotopy_projection (p : E ⟶ B) (β : (Δ[1] : SSet.{u}) ⟶ B)
    (hτ : τ ≫ p = stdSimplex.σ (1 : Fin 2) ≫ β) :
    (sourceFixedTriangleHomotopy τ).h ≫ p = fst (Δ[1] : SSet.{u}) Δ[1] ≫ β :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableTriangleComparisonShape ≫ z) hτ).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z ↦ z ≫ β) sourceFixedTriangleShape_base)))

/-- 元の初期図式を指定すれば、円柱はその同じ初期図式を全時刻で保つ。 -/
lemma sourceFixedTriangleHomotopy_initial (v : (Δ[0] : SSet.{u}) ⟶ E)
    (hτ : (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ≫ τ = v) :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ (sourceFixedTriangleHomotopy τ).h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ v :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ τ) sourceFixedTriangleShape_initial).trans
      ((Category.assoc _ _ _).trans (congrArg (fun z ↦ fst (Δ[0] : SSet.{u}) Δ[1] ≫ z) hτ)))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
