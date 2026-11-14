module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSquareTopMiddleData
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquarePrismGluing

/-! # 零角側の中間対象を変える実四角形ホモトピー

概要：上辺の因子分解に沿って左上の対象を変え、下側三角形を固定する。
方針：上側の中間対象比較と下側の定値ホモトピーを対角で貼る。
規約：実二単体と対角の固定式を保持。使われ方：cone 四角形の零角の変更。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {W X Y Y' Z : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}
variable (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData A D W X Y Z) (m : Y ⟶ Y') (r : Y' ⟶ Z) (hr : m ≫ r = s.top)

/-- 上側比較と下側の定値ホモトピーは対角で一致する。 -/
lemma changeTopMiddleHomotopy_compatible :
    ((SSet.stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
      (s.changeTopMiddleUpperHomotopy m r hr).h =
    ((SSet.stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
      (CartesianMonoidalCategory.fst (Δ[2] : SSet.{max (u + 1) v}) Δ[1] ≫
        SSet.yonedaEquiv.symm s.lowerTriangle) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.changeTopMiddleUpperHomotopy_diagonal]
  exact congrArg (fun q => CartesianMonoidalCategory.fst
    (Δ[1] : SSet.{max (u + 1) v}) Δ[1] ≫ q) s.triangles_compatible

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeTopMiddleHomotopy_compatible)


/-- 左上の中間対象を変える四角形全体の実ホモトピー。 -/
def changeTopMiddleHomotopy : SSet.Homotopy s.square (s.changeTopMiddle m r hr).square where
  h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.desc (s.changeTopMiddleUpperHomotopy m r hr).h
    (CartesianMonoidalCategory.fst (Δ[2] : SSet.{max (u + 1) v}) Δ[1] ≫
      SSet.yonedaEquiv.symm s.lowerTriangle) (s.changeTopMiddleHomotopy_compatible m r hr)
  h₀ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.inl_desc]
      exact (s.changeTopMiddleUpperHomotopy m r hr).h₀.trans s.square_upper.symm
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.inr_desc,
        ← Category.assoc, SSet.ι₀_fst, Category.id_comp]
      exact s.square_lower.symm
  h₁ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.inl_desc]
      exact (s.changeTopMiddleUpperHomotopy m r hr).h₁.trans
        (s.changeTopMiddle m r hr).square_upper.symm
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.inr_desc,
        ← Category.assoc, SSet.ι₁_fst, Category.id_comp]
      exact (s.changeTopMiddle m r hr).square_lower.symm
  rel := by
    ext n q
    exact False.elim q.1.2

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeTopMiddleHomotopy)


/-- 比較は下側三角形の全体を固定する。 -/
lemma changeTopMiddleHomotopy_lower :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
      (s.changeTopMiddleHomotopy m r hr).h =
    CartesianMonoidalCategory.fst (Δ[2] : SSet.{max (u + 1) v}) Δ[1] ≫
      SSet.yonedaEquiv.symm s.lowerTriangle :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.inr_desc _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeTopMiddleHomotopy_lower)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
