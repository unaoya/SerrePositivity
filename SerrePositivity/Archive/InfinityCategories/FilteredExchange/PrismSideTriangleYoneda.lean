module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TrianglePrismLowerSides
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square

/-!
概要：三角柱の側面の元の二単体を、同じ辺の全正方形の標準三角形で表示する。
方針：元の辺の自然性と標準正方形の二つの単体の座標を照合する。
規約：全二単体の厳密な一致。使われ方：元の単位正方形との側面の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 上側の側面は、同じ全辺正方形の第零標準三角形そのもの。 -/
lemma homotopyEdgeTriangleUpper_yoneda {P Y : SSet.{u}} (H : P ⊗ Δ[1] ⟶ Y)
    (k : (Δ[1] : SSet.{u}) ⟶ P) :
    homotopyEdgeTriangleUpper H (SSet.yonedaEquiv k) =
      SSet.yonedaEquiv (squareTriangle 0 ≫ (k ▷ Δ[1]) ≫ H) := by
  have hs : SSet.yonedaEquiv (squareTriangle.{u} 0) =
      ((Δ[1] : SSet.{u}).σ 0 (SSet.yonedaEquiv (𝟙 Δ[1])),
        (Δ[1] : SSet.{u}).σ 1 (SSet.yonedaEquiv (𝟙 Δ[1]))) := by
    apply Prod.ext <;> decide
  rw [SSet.yonedaEquiv_comp, hs]
  change H.app (Opposite.op ⦋2⦌) (_, _) = H.app (Opposite.op ⦋2⦌) (_, _)
  congr 1
  apply Prod.ext
  · change P.map (SimplexCategory.σ (0 : Fin 2)).op (SSet.yonedaEquiv k) =
      k.app (Opposite.op ⦋2⦌) ((Δ[1] : SSet.{u}).σ 0 (SSet.yonedaEquiv (𝟙 Δ[1])))
    have hk : k.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 Δ[1])) =
        SSet.yonedaEquiv k := by rw [← SSet.yonedaEquiv_comp, Category.id_comp]
    have h := ConcreteCategory.congr_hom (k.naturality (SimplexCategory.σ (0 : Fin 2)).op)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
    change k.app (Opposite.op ⦋2⦌) ((Δ[1] : SSet.{u}).σ 0
      (SSet.yonedaEquiv (𝟙 Δ[1]))) = P.map (SimplexCategory.σ (0 : Fin 2)).op
        (k.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 Δ[1]))) at h
    rw [hk] at h
    exact h.symm
  · rfl

/-- 下側の側面は、同じ全辺正方形の第一標準三角形そのもの。 -/
lemma homotopyEdgeTriangleLower_yoneda {P Y : SSet.{u}} (H : P ⊗ Δ[1] ⟶ Y)
    (k : (Δ[1] : SSet.{u}) ⟶ P) :
    homotopyEdgeTriangleLower H (SSet.yonedaEquiv k) =
      SSet.yonedaEquiv (squareTriangle 1 ≫ (k ▷ Δ[1]) ≫ H) := by
  have hs : SSet.yonedaEquiv (squareTriangle.{u} 1) =
      ((Δ[1] : SSet.{u}).σ 1 (SSet.yonedaEquiv (𝟙 Δ[1])),
        (Δ[1] : SSet.{u}).σ 0 (SSet.yonedaEquiv (𝟙 Δ[1]))) := by
    apply Prod.ext <;> decide
  rw [SSet.yonedaEquiv_comp, hs]
  change H.app (Opposite.op ⦋2⦌) (_, _) = H.app (Opposite.op ⦋2⦌) (_, _)
  congr 1
  apply Prod.ext
  · change P.map (SimplexCategory.σ (1 : Fin 2)).op (SSet.yonedaEquiv k) =
      k.app (Opposite.op ⦋2⦌) ((Δ[1] : SSet.{u}).σ 1 (SSet.yonedaEquiv (𝟙 Δ[1])))
    have hk : k.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 Δ[1])) =
        SSet.yonedaEquiv k := by rw [← SSet.yonedaEquiv_comp, Category.id_comp]
    have h := ConcreteCategory.congr_hom (k.naturality (SimplexCategory.σ (1 : Fin 2)).op)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
    change k.app (Opposite.op ⦋2⦌) ((Δ[1] : SSet.{u}).σ 1
      (SSet.yonedaEquiv (𝟙 Δ[1]))) = P.map (SimplexCategory.σ (1 : Fin 2)).op
        (k.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 Δ[1]))) at h
    rw [hk] at h
    exact h.symm
  · rfl

/-- 座標順の交換は、元の二つの標準三角形を厳密に交換する。 -/
lemma squareTriangle_swap (i : Fin 2) :
    squareTriangle.{u} i ≫ (β_ Δ[1] Δ[1]).hom = squareTriangle (1 - i) := by
  apply SSet.yonedaEquiv.injective
  fin_cases i <;> apply Prod.ext <;> decide

end SerrePositivity.InfinityCategories.F2
