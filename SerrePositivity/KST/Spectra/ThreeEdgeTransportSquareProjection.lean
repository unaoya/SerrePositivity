module

public import SerrePositivity.KST.Spectra.ThreeEdgeTransportSquare
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.ThreeEdgeTransportRelabel

/-!
概要：三辺輸送の正方形を、元の三角形単体の射影と端点表示の変更に照合する。
方針：正方形の pushout の二つの脚で、保存した二単体そのものを比較する。
規約：四辺と二つの三角形を選び直さない。使われ方：非零境界への正方形全体の射影。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.ThreeEdgeTransport
variable {Z : SSet.{u}} {x a y b : Z _⦋0⦌}
  {left : Z.Edge x a} {middle : Z.Edge x y} {right : Z.Edge y b}
  (D : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport left middle right)

/-- 元の二単体が同じなら、端点表示にかかわらず正方形全体が同じ。 -/
lemma square_eq_of_simplex_eq {x' a' y' b' : Z _⦋0⦌}
    {left' : Z.Edge x' a'} {middle' : Z.Edge x' y'} {right' : Z.Edge y' b'}
    (D' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ThreeEdgeTransport left' middle' right')
    (hfirst : D.first.simplex = D'.first.simplex)
    (hsecond : D.second.simplex = D'.second.simplex) : (_root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.square D) = (_root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.square D') := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.hom_ext
  · rw [square_upper, square_upper, hfirst]
  · rw [square_lower, square_lower, hsecond]

/-- 正方形を写すと、同じ二単体を写して作った正方形そのもの。 -/
lemma square_map {W : SSet.{u}} (p : Z ⟶ W) : (_root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.square D) ≫ p = (_root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.square (D.map p)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.hom_ext
  · rw [← Category.assoc, square_upper, square_upper]
    exact SSet.yonedaEquiv_symm_comp D.first.simplex p
  · rw [← Category.assoc, square_lower, square_lower]
    exact SSet.yonedaEquiv_symm_comp D.second.simplex p

/-- 元の一次単体を保つ端点表示の変更は、正方形全体を厳密に保つ。 -/
lemma square_relabel {x' a' y' b' : Z _⦋0⦌}
    (left' : Z.Edge x' a') (middle' : Z.Edge x' y') (right' : Z.Edge y' b')
    (hl : left.edge = left'.edge) (hm : middle.edge = middle'.edge)
    (hr : right.edge = right'.edge) :
    (_root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.square (D.relabel left' middle' right' hl hm hr)) = (_root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.square D) :=
  square_eq_of_simplex_eq _ _ rfl rfl

end SerrePositivity.KST.Spectra.ThreeEdgeTransport
