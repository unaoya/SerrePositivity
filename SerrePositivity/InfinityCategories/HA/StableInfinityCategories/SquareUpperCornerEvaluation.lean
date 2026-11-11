module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FixedMapHomotopyEvaluation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonComposition

/-! # 上三角形を固定する正方形ホモトピーの両端成分

概要：上三角形を固定した正方形比較は始点と終点で恒等成分を持つ。
方針：上三角形の両端頂点を正方形の両端角と同定し、固定部分の評価を使う。
規約：quasicategory 性は不要。使われ方：D7 の右下だけを変える四角形比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 上三角形の二つの外側頂点は正方形の始点・終点。 -/
lemma squareTriangle_upper_corner (i : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 0).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (if i = 0 then (0 : Fin 3) else 2)) =
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) i i := by
  fin_cases i <;> apply Prod.ext <;> decide

/-- 上三角形を固定する正方形の射は両端角で恒等成分を持つ。 -/
lemma squareUpperConstantHomotopy_corner_arrow {X : SSet.{u}}
    {F G : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X} (H : SSet.Homotopy F G)
    (hU : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.fst (Δ[2] : SSet.{u}) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ F)
    (i : Fin 2) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X i i).map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))) =
      Arrow.mk (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex F i i)) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homotopyEvaluation_fixed_map_arrow H (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0) hU
    (stdSimplex.obj₀Equiv.symm (if i = 0 then (0 : Fin 3) else 2))
  rw [squareTriangle_upper_corner] at h
  exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
