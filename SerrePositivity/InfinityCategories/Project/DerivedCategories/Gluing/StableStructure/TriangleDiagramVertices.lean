module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.TriangleDiagramParameterTransport
/-! # 実三角形図式の頂点と六つの辺端点

概要：実二単体の三頂点を保持し、全ての面の始点と終点を同じ頂点へ照合する。
方針：Yoneda 表示と有限の標準面の作用を計算する。
規約：辺や頂点の代表を選び直さない。
使われ方：六片の共有辺から五頂点上の合成図式を構成する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet
open scoped _root_.Simplicial

def dgGluingTriangleVertex {Z : SSet.{u}} (T : (Δ[2] : SSet.{u}) ⟶ Z) (i : Fin 3) :
    Z _⦋0⦌ := T.app _ (stdSimplex.obj₀Equiv.symm i)

lemma dgGluingTriangleFace_source {Z : SSet.{u}} (T : (Δ[2] : SSet.{u}) ⟶ Z)
    (i : Fin 3) : Z.δ 1 (SSet.yonedaEquiv (stdSimplex.δ i ≫ T)) =
      dgGluingTriangleVertex T (![1, 0, 0] i) := by
  rw [← stdSimplex.yonedaEquiv_δ_comp]
  change _ = T.app _ _
  rw [← Category.assoc]
  change T.app _ _ = T.app _ _
  apply congrArg (T.app (Opposite.op ⦋0⦌))
  apply SSet.stdSimplex.ext
  intro j
  fin_cases i <;> fin_cases j <;> rfl

lemma dgGluingTriangleFace_target {Z : SSet.{u}} (T : (Δ[2] : SSet.{u}) ⟶ Z)
    (i : Fin 3) : Z.δ 0 (SSet.yonedaEquiv (stdSimplex.δ i ≫ T)) =
      dgGluingTriangleVertex T (![2, 2, 1] i) := by
  rw [← stdSimplex.yonedaEquiv_δ_comp]
  change _ = T.app _ _
  rw [← Category.assoc]
  change T.app _ _ = T.app _ _
  apply congrArg (T.app (Opposite.op ⦋0⦌))
  apply SSet.stdSimplex.ext
  intro j
  fin_cases i <;> fin_cases j <;> rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
