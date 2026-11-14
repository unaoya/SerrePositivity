module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSquareData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Triangles.DGModuleTriangleMiddleHomotopy

/-! # 四角形の左上の中間対象の変更

概要：上辺の因子分解に沿って左上の頂点を変更し、対角と上下のホモトピーを保つ。
方針：上三角形を中間対象の比較三単体で動かし、下三角形は定値に保つ。
規約：全て実際の単体的ホモトピー。使われ方：β3 の cone 四角形の零角変更。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {W X Y Y' Z : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}
variable (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData A D W X Y Z) (m : Y ⟶ Y') (r : Y' ⟶ Z) (hr : m ≫ r = s.top)

/-- 上辺の因子分解による左上の頂点の変更。 -/
def changeTopMiddle : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData A D W X Y' Z where
  bottom := s.bottom
  left := s.left ≫ m
  right := s.right
  top := r
  diagonal := s.diagonal
  upperHomotopy := s.upperHomotopy
  lowerHomotopy := s.lowerHomotopy
  upperEquation := by simpa only [Category.assoc, hr] using s.upperEquation
  lowerEquation := s.lowerEquation

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeTopMiddle)


private lemma triangle_congr_right {W X Z : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}
    (a : W ⟶ X) (b b' : X ⟶ Z) (c : W ⟶ Z)
    (t : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Z) (-1))
    (ht : (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Z)).d (-1) 0 t =
        (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (a ≫ b))).val -
        (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) c)).val)
    (ht' : (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) W)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) Z)).d (-1) 0 t =
        (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (a ≫ b'))).val -
        (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) c)).val)
    (hb : b = b') : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D a b c t ht).simplex =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D a b' c t ht').simplex := by
  cases hb
  rfl

/-- 中間対象比較の始端は元の上三角形。 -/
lemma changeTopMiddle_sourceTriangle :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D s.left (m ≫ r) s.diagonal s.upperHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleMiddle_sourceEquation A D s.left m r s.diagonal s.upperHomotopy
        (s.changeTopMiddle m r hr).upperEquation)).simplex = s.upperTriangle := by
  exact triangle_congr_right s.left (m ≫ r) s.top s.diagonal s.upperHomotopy _ _ hr

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeTopMiddle_sourceTriangle)


/-- 上三角形の中間対象を変更する実際のホモトピー。 -/
def changeTopMiddleUpperHomotopy : SSet.Homotopy (Y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)
    (SSet.yonedaEquiv.symm s.upperTriangle)
    (SSet.yonedaEquiv.symm (s.changeTopMiddle m r hr).upperTriangle) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleMiddleHomotopy A D s.left m r s.diagonal s.upperHomotopy
    (s.changeTopMiddle m r hr).upperEquation).h
  h₀ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleMiddleHomotopy A D s.left m r s.diagonal s.upperHomotopy
    (s.changeTopMiddle m r hr).upperEquation).h₀.trans
      (congrArg SSet.yonedaEquiv.symm (s.changeTopMiddle_sourceTriangle m r hr))
  h₁ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleMiddleHomotopy A D s.left m r s.diagonal s.upperHomotopy
    (s.changeTopMiddle m r hr).upperEquation).h₁
  rel := by
    ext n q
    exact False.elim q.1.2

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeTopMiddleUpperHomotopy)


/-- 中間対象変更のホモトピーは対角を固定する。 -/
lemma changeTopMiddleUpperHomotopy_diagonal :
    ((SSet.stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
        (s.changeTopMiddleUpperHomotopy m r hr).h =
      CartesianMonoidalCategory.fst (Δ[1] : SSet.{max (u + 1) v}) Δ[1] ≫
        SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm s.upperTriangle := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleTriangleMiddleHomotopy_diagonal A D s.left m r s.diagonal s.upperHomotopy
    (s.changeTopMiddle m r hr).upperEquation).trans
      (congrArg (fun z => CartesianMonoidalCategory.fst (Δ[1] : SSet.{max (u + 1) v}) Δ[1] ≫
        SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm z)
          (s.changeTopMiddle_sourceTriangle m r hr))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeTopMiddleUpperHomotopy_diagonal)


/-- 下三角形は中間対象の変更で変わらない。 -/
lemma changeTopMiddle_lowerTriangle :
    (s.changeTopMiddle m r hr).lowerTriangle = s.lowerTriangle := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeTopMiddle_lowerTriangle)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
