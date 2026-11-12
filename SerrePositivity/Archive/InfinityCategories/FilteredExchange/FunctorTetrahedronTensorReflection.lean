module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTetrahedronPostReindexReflection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices

/-!
概要：元の六 native 作用と四面の指定三角形比較を、全始域の底上の制限に沿って保持する。
方針：六辺の厳密な交換と四面の指定成分の自然性を同じ制限データへ束ねる。
規約：元の指定値を再選択しない。使われ方：三つの全選択族の指定関係を共通全空間へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} {F₀ F₁ F₂ F₃ : B ⟶ SpaceInfinity.{u}}
  {a₀₁ : SSet.Homotopy F₀ F₁} {a₁₂ : SSet.Homotopy F₁ F₂} {a₂₃ : SSet.Homotopy F₂ F₃}
  {a₀₂ : SSet.Homotopy F₀ F₂} {a₁₃ : SSet.Homotopy F₁ F₃} {a₀₃ : SSet.Homotopy F₀ F₃}
  (T₀₁₂ : FunctorCompositionTriangle a₀₁ a₁₂ a₀₂)
  (T₁₂₃ : FunctorCompositionTriangle a₁₂ a₂₃ a₁₃)
  (T₀₁₃ : FunctorCompositionTriangle a₀₁ a₁₃ a₀₃)
  (T₀₂₃ : FunctorCompositionTriangle a₀₂ a₂₃ a₀₃)
  {K : SSet.{u + 1}} (v : K _⦋0⦌)
local notation "E" => leftUnstraightening F₀
local notation "p" => leftUnstraighteningProjection F₀
local notation "d" => fst E K ≫ p
local notation "x₀" => relativeFunctorVertex p p (𝟙 E) (Category.id_comp p)
local notation "xₖ" => relativeFunctorVertex p d (fst E K) rfl

include v in
/-- 全係数を保持した指定三関係は、その係数の一点による切断で元の全空間へ反映される。 -/
lemma functorTetrahedronPostComparison_square_of_tensor_pre
    (h : (functorTriangleSequentialPostComparison T₀₁₃ d).app xₖ ≪≫
        (functorTriangleSequentialPostComparison T₁₂₃ d).app
          ((functorHomotopyRelativePost a₀₁ d).app _ xₖ) =
      (functorTriangleSequentialPostComparison T₀₂₃ d).app xₖ ≪≫
        VertexIso.map ((functorTriangleSequentialPostComparison T₀₁₂ d).app xₖ)
          (functorHomotopyRelativePost a₂₃ d)) :
    (functorTriangleSequentialPostComparison T₀₁₃ p).app x₀ ≪≫
        (functorTriangleSequentialPostComparison T₁₂₃ p).app
          ((functorHomotopyRelativePost a₀₁ p).app _ x₀) =
      (functorTriangleSequentialPostComparison T₀₂₃ p).app x₀ ≪≫
        VertexIso.map ((functorTriangleSequentialPostComparison T₀₁₂ p).app x₀)
          (functorHomotopyRelativePost a₂₃ p) := by
  have hx : (relativeFunctorOverPre p
      (Over.homMk (U := Over.mk d) (V := Over.mk p) (fst E K) rfl)).app _ x₀ = xₖ := by
    have hi := relativeFunctorOverPre_vertex p
      (Over.homMk (U := Over.mk d) (V := Over.mk p) (fst E K) rfl)
      (𝟙 E) (Category.id_comp p)
    exact hi.trans (by
      apply Subtype.ext
      exact congrArg functorVertex (Category.comp_id (fst E K)))
  refine functorTetrahedronPostComparison_square_of_reindexed T₀₁₂ T₁₂₃ T₀₁₃ T₀₂₃
    p d (fst E K) rfl (lift (𝟙 E) (SSet.const v)) ?_ ?_ x₀ ?_
  · rw [← Category.assoc, lift_fst, Category.id_comp]
  · exact lift_fst _ _
  · rw [← hx] at h
    exact h

end SerrePositivity.InfinityCategories.F2
