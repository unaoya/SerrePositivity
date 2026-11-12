module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.JoinTensorInterval
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofFirstHornPrism

/-! # 始点を重ねた三角形の全辺の計算

概要：二次の零退化は第一辺を始点へ潰し、対角と第二辺を元の区間へ戻す。
方針：標準単体の有限順序写像と直積の射影を計算する。
規約：単体集合の射の厳密等式。使われ方：境界上で比較を定値にする相対三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

/-- 第一辺は零頂点への退化辺になる。 -/
lemma roofFirstTriangleCollapse_edge01 :
    SSet.stdSimplex.δ (2 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) =
      SSet.stdSimplex.σ (0 : Fin 1) ≫ SSet.stdSimplex.δ (1 : Fin 2) := by
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ =
    SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  decide

/-- 対角は区間全体を回収する。 -/
lemma roofFirstTriangleCollapse_edge02 :
    SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) =
      𝟙 (Δ[1] : SSet.{u}) := by
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ = _
  rw [← Functor.map_comp]
  exact (congrArg SSet.stdSimplex.map (by decide :
    SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) = 𝟙 _)).trans
      (SSet.stdSimplex.map_id _)

/-- 第二辺も区間全体を回収する。 -/
lemma roofFirstTriangleCollapse_edge12 :
    SSet.stdSimplex.δ (0 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) =
      𝟙 (Δ[1] : SSet.{u}) := by
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ = _
  rw [← Functor.map_comp]
  exact (congrArg SSet.stdSimplex.map (by decide :
    SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) = 𝟙 _)).trans
      (SSet.stdSimplex.map_id _)

/-- 零頂点を繰り返す退化区間上の辺族は、始端に定値な族。 -/
lemma roofIntervalReset_zero {L E : SSet.{u}} {f g : L ⟶ E} (T : SSet.Homotopy f g) :
    (L ◁ SSet.stdSimplex.σ (0 : Fin 1)) ≫
      (L ◁ SSet.stdSimplex.δ (1 : Fin 2)) ≫ T.h = fst L Δ[1] ≫ f := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.fst_stdSimplexZero_comp_ι₀, Category.assoc, T.h₀,
    ← Category.assoc, whiskerLeft_fst]

/-- 第二辺の始端は第一辺の終端。 -/
lemma roofFirstTriangle_edge12_source (L : SSet.{u}) :
    SSet.ι₀ ≫ (L ◁ SSet.stdSimplex.δ (0 : Fin 3)) =
      SSet.ι₁ ≫ (L ◁ SSet.stdSimplex.δ (2 : Fin 3)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro k
    rfl

/-- 第二辺の終端は対角の終端。 -/
lemma roofFirstTriangle_edge12_target (L : SSet.{u}) :
    SSet.ι₁ ≫ (L ◁ SSet.stdSimplex.δ (0 : Fin 3)) =
      SSet.ι₁ ≫ (L ◁ SSet.stdSimplex.δ (1 : Fin 3)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro k
    rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
