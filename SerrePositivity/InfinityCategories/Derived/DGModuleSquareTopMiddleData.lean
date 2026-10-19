module
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquareData
public import SerrePositivity.InfinityCategories.Derived.DGModuleTriangleMiddleHomotopy

/-! # 四角形の左上の中間対象の変更

概要：上辺の因子分解に沿って左上の頂点を変更し、対角と上下のホモトピーを保つ。
方針：上三角形を中間対象の比較三単体で動かし、下三角形は定値に保つ。
規約：全て実際の単体的ホモトピー。使われ方：β3 の cone 四角形の零角変更。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGModuleSquareData
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
variable {W X Y Y' Z : ModuleCategory A D}
variable (s : DGModuleSquareData A D W X Y Z) (m : Y ⟶ Y') (r : Y' ⟶ Z) (hr : m ≫ r = s.top)

/-- 上辺の因子分解による左上の頂点の変更。 -/
def changeTopMiddle : DGModuleSquareData A D W X Y' Z where
  bottom := s.bottom
  left := s.left ≫ m
  right := s.right
  top := r
  diagonal := s.diagonal
  upperHomotopy := s.upperHomotopy
  lowerHomotopy := s.lowerHomotopy
  upperEquation := by simpa only [Category.assoc, hr] using s.upperEquation
  lowerEquation := s.lowerEquation

private lemma triangle_congr_right {W X Z : ModuleCategory A D}
    (a : W ⟶ X) (b b' : X ⟶ Z) (c : W ⟶ Z)
    (t : GradedHom A (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Z) (-1))
    (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Z)).d (-1) 0 t =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val)
    (ht' : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Z)).d (-1) 0 t =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b'))).val -
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val)
    (hb : b = b') : (dgModuleCompStruct A D a b c t ht).simplex =
      (dgModuleCompStruct A D a b' c t ht').simplex := by
  cases hb
  rfl

/-- 中間対象比較の始端は元の上三角形。 -/
lemma changeTopMiddle_sourceTriangle :
    (dgModuleCompStruct A D s.left (m ≫ r) s.diagonal s.upperHomotopy
      (dgModuleTriangleMiddle_sourceEquation A D s.left m r s.diagonal s.upperHomotopy
        (s.changeTopMiddle m r hr).upperEquation)).simplex = s.upperTriangle := by
  exact triangle_congr_right s.left (m ≫ r) s.top s.diagonal s.upperHomotopy _ _ hr

/-- 上三角形の中間対象を変更する実際のホモトピー。 -/
def changeTopMiddleUpperHomotopy : SSet.Homotopy (Y := dgModuleNerve A D)
    (SSet.yonedaEquiv.symm s.upperTriangle)
    (SSet.yonedaEquiv.symm (s.changeTopMiddle m r hr).upperTriangle) where
  h := (dgModuleTriangleMiddleHomotopy A D s.left m r s.diagonal s.upperHomotopy
    (s.changeTopMiddle m r hr).upperEquation).h
  h₀ := (dgModuleTriangleMiddleHomotopy A D s.left m r s.diagonal s.upperHomotopy
    (s.changeTopMiddle m r hr).upperEquation).h₀.trans
      (congrArg SSet.yonedaEquiv.symm (s.changeTopMiddle_sourceTriangle m r hr))
  h₁ := (dgModuleTriangleMiddleHomotopy A D s.left m r s.diagonal s.upperHomotopy
    (s.changeTopMiddle m r hr).upperEquation).h₁
  rel := by
    ext n q
    exact False.elim q.1.2

/-- 中間対象変更のホモトピーは対角を固定する。 -/
lemma changeTopMiddleUpperHomotopy_diagonal :
    ((SSet.stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
        (s.changeTopMiddleUpperHomotopy m r hr).h =
      CartesianMonoidalCategory.fst (Δ[1] : SSet.{max (u + 1) v}) Δ[1] ≫
        SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm s.upperTriangle := by
  exact (dgModuleTriangleMiddleHomotopy_diagonal A D s.left m r s.diagonal s.upperHomotopy
    (s.changeTopMiddle m r hr).upperEquation).trans
      (congrArg (fun z => CartesianMonoidalCategory.fst (Δ[1] : SSet.{max (u + 1) v}) Δ[1] ≫
        SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm z)
          (s.changeTopMiddle_sourceTriangle m r hr))

/-- 下三角形は中間対象の変更で変わらない。 -/
lemma changeTopMiddle_lowerTriangle :
    (s.changeTopMiddle m r hr).lowerTriangle = s.lowerTriangle := rfl

end SerrePositivity.InfinityCategories.DGModuleSquareData
