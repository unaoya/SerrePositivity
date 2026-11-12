module
public import SerrePositivity.KST.SConstruction.CoherentSquareMappingTriangles

/-! # Square の境界の射と元の raw な辺の照合
概要：元の四つの境界射から、二つの三角形を切り出すための raw な辺の等式を得る。
方針：標準区間の辺と恒等単体を Yoneda の表示に直接合わせる。
規約：値域の充填性は不要。
使われ方：元の suspension 自然性 square を二つの実三角形へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- square の水平の raw な辺は、同じ境界射の Yoneda 表示。 -/
lemma squareHorizontalEdge_yoneda {Z : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Z) (t : Fin 2) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.tensor (SSet.Truncated.Edge.id
      (X := (truncation 2).obj (Δ[1] : SSet.{u}))
      (SSet.stdSimplex.obj₀Equiv.symm t))).map ((truncation 2).map Q)).edge =
      SSet.yonedaEquiv (lift (𝟙 (Δ[1] : SSet.{u}))
        (SSet.const (SSet.stdSimplex.obj₀Equiv.symm t)) ≫ Q) := by
  apply congrArg (Q.app (Opposite.op ⦋1⦌))
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro k <;> fin_cases k <;> rfl

/-- square の垂直の raw な辺は、同じ境界射の Yoneda 表示。 -/
lemma squareVerticalEdge_yoneda {Z : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Z) (t : Fin 2) :
    (((SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u}))
      (SSet.stdSimplex.obj₀Equiv.symm t)).tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map
        ((truncation 2).map Q)).edge =
      SSet.yonedaEquiv (lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm t))
        (𝟙 (Δ[1] : SSet.{u})) ≫ Q) := by
  apply congrArg (Q.app (Opposite.op ⦋1⦌))
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro k <;> fin_cases k <;> rfl

/-- 四つの元の境界射から、同じ対角辺と二つの標準三角形を厳密に回収する。 -/
def coherentSquareMappingTrianglesOfBoundary
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X₀ X₁ Y₀ Y₁ : C} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) (l : X₀ ⟶ Y₀) (r : X₁ ⟶ Y₁)
    (Q : (Δ[1] : SSet.{max u v}) ⊗ Δ[1] ⟶ SimplicialNerve C)
    (hb : SSet.ι₀ ≫ Q = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
    (ht : SSet.ι₁ ≫ Q = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge)
    (hl : lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (𝟙 (Δ[1] : SSet.{max u v})) ≫ Q = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge l).edge)
    (hr : lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (𝟙 (Δ[1] : SSet.{max u v})) ≫ Q = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge r).edge) :
    CoherentSquareMappingTriangles f g l r := by
  refine coherentSquareMappingTrianglesOfEdges f g l r Q ?_ ?_ ?_ ?_
  · rw [squareHorizontalEdge_yoneda]
    change SSet.yonedaEquiv (SSet.ι₀ ≫ Q) = _
    rw [hb, Equiv.apply_symm_apply]
  · rw [squareHorizontalEdge_yoneda]
    change SSet.yonedaEquiv (SSet.ι₁ ≫ Q) = _
    rw [ht, Equiv.apply_symm_apply]
  · rw [squareVerticalEdge_yoneda, hl, Equiv.apply_symm_apply]
  · rw [squareVerticalEdge_yoneda, hr, Equiv.apply_symm_apply]

end SerrePositivity.KST.SConstruction
