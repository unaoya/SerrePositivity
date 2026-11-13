module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.ComplexHomotopies.ComplexSquareData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.TriangleMiddleHomotopy

/-! # 四角形の右下の中間対象の変更

概要：右辺の因子分解に沿って右下の頂点を変更し、対角と上下のホモトピーを保つ。
方針：下三角形を中間対象の比較三単体で動かし、上三角形は定値に保つ。
規約：全て実際の単体的ホモトピー。使われ方：D7 の cofiber から suspension への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B B' C D : _root_.SerrePositivity.DifferentialGraded.Complex S}
variable (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData A B C D) (m : B ⟶ B') (r : B' ⟶ D) (hr : m ≫ r = s.right)

/-- 右辺の因子分解による右下の頂点の変更。 -/
def changeBottomMiddle : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData A B' C D where
  bottom := s.bottom ≫ m
  left := s.left
  right := r
  top := s.top
  diagonal := s.diagonal
  lowerHomotopy := s.lowerHomotopy
  upperHomotopy := s.upperHomotopy
  lowerEquation := by simpa only [Category.assoc, hr] using s.lowerEquation
  upperEquation := s.upperEquation

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeBottomMiddle)


/-- 中間対象比較の始端は元の下三角形。 -/
lemma changeBottomMiddle_sourceTriangle :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct s.bottom (m ≫ r) s.diagonal s.lowerHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddle_sourceEquation s.bottom m r s.diagonal s.lowerHomotopy
        (s.changeBottomMiddle m r hr).lowerEquation)).simplex = s.lowerTriangle := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · rfl
  · exact heq_of_eq rfl
  · exact heq_of_eq (congrArg Cochain.ofHom hr)
  · exact heq_of_eq rfl
  · exact heq_of_eq rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeBottomMiddle_sourceTriangle)


/-- 下三角形の中間対象を変更する実際のホモトピー。 -/
def changeBottomMiddleLowerHomotopy : SSet.Homotopy (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))
    (SSet.yonedaEquiv.symm s.lowerTriangle)
    (SSet.yonedaEquiv.symm (s.changeBottomMiddle m r hr).lowerTriangle) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddleHomotopy s.bottom m r s.diagonal s.lowerHomotopy
    (s.changeBottomMiddle m r hr).lowerEquation).h
  h₀ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddleHomotopy s.bottom m r s.diagonal s.lowerHomotopy
    (s.changeBottomMiddle m r hr).lowerEquation).h₀.trans
      (congrArg SSet.yonedaEquiv.symm (s.changeBottomMiddle_sourceTriangle m r hr))
  h₁ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddleHomotopy s.bottom m r s.diagonal s.lowerHomotopy
    (s.changeBottomMiddle m r hr).lowerEquation).h₁
  rel := by
    ext n q
    exact False.elim q.1.2

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeBottomMiddleLowerHomotopy)


/-- 中間対象変更のホモトピーは対角を固定する。 -/
lemma changeBottomMiddleLowerHomotopy_diagonal :
    ((SSet.stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{u + 1})) ≫
        (s.changeBottomMiddleLowerHomotopy m r hr).h =
      CartesianMonoidalCategory.fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
        SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm s.lowerTriangle := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangleMiddleHomotopy_diagonal s.bottom m r s.diagonal s.lowerHomotopy
    (s.changeBottomMiddle m r hr).lowerEquation).trans
      (congrArg (fun z => CartesianMonoidalCategory.fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
        SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm z)
          (s.changeBottomMiddle_sourceTriangle m r hr))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeBottomMiddleLowerHomotopy_diagonal)


/-- 上三角形は中間対象の変更で変わらない。 -/
lemma changeBottomMiddle_upperTriangle :
    (s.changeBottomMiddle m r hr).upperTriangle = s.upperTriangle := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeBottomMiddle_upperTriangle)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
