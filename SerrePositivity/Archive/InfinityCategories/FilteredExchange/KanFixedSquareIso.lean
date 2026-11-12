module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanFixedSquareDiagonal
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTriangleIsoFacesEquality

/-!
概要：両端固定の空間の全正方形を、その二三角形を保つ Kan 射の同型に移す。
方針：同じ対角を共有する上下の精密化の同型を合成する。
規約：辺の類から別のホモトピーを選ばない。使われ方：指定辺比較の二単体の追跡。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {X Y : KanObject.{u}} (f g : X ⟶ Y)
  (Q : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ SpaceInfinity.{u})
  (hb : SSet.yonedaEquiv (SSet.ι₀ ≫ Q) = (coherentNerveEdge f).edge)
  (ht : SSet.yonedaEquiv (SSet.ι₁ ≫ Q) = (coherentNerveEdge g).edge)

/-- 元の上二単体から、その対角と左恒等辺・元の上辺の合成を比較する。 -/
def kanFixedSquareUpperIso
    (hl : SSet.yonedaEquiv (prismEndpoint 0 Δ[1] ≫ Q) = (coherentNerveEdge (𝟙 X)).edge) :
    FunctorIso (kanFixedSquareDiagonal f g Q hb ht) (𝟙 X ≫ g) :=
  spaceInfinityTriangleIso_of_faces (𝟙 X) g (kanFixedSquareDiagonal f g Q hb ht)
    (SSet.yonedaEquiv (squareTriangle 0 ≫ Q))
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, triangleSquare_upper_left]
      exact hl)
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, triangleSquare_upper_top]
      exact ht)
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, squareTriangle_diagonal]
      exact (kanFixedSquareDiagonal_edge f g Q hb ht).symm)

/-- 元の下二単体から、その対角と元の下辺・右恒等辺の合成を比較する。 -/
def kanFixedSquareLowerIso
    (hr : SSet.yonedaEquiv (prismEndpoint 1 Δ[1] ≫ Q) = (coherentNerveEdge (𝟙 Y)).edge) :
    FunctorIso (kanFixedSquareDiagonal f g Q hb ht) (f ≫ 𝟙 Y) :=
  spaceInfinityTriangleIso_of_faces f (𝟙 Y) (kanFixedSquareDiagonal f g Q hb ht)
    (SSet.yonedaEquiv (squareTriangle 1 ≫ Q))
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, triangleSquare_lower_bottom]
      exact hb)
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, triangleSquare_lower_right]
      exact hr)
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, squareTriangle_diagonal]
      exact (kanFixedSquareDiagonal_edge f g Q hb ht).symm)

/-- 同じ正方形の下三角形の逆と上三角形を合成した、元の上下 Kan 射の比較同型。 -/
def kanFixedSquareValueIso
    (hl : SSet.yonedaEquiv (prismEndpoint 0 Δ[1] ≫ Q) = (coherentNerveEdge (𝟙 X)).edge)
    (hr : SSet.yonedaEquiv (prismEndpoint 1 Δ[1] ≫ Q) = (coherentNerveEdge (𝟙 Y)).edge) :
    FunctorIso f g :=
  (functorIsoOfEq (kanFixedSquareLowerIso f g Q hb ht hr) rfl (Category.comp_id _)).symm ≪≫
    functorIsoOfEq (kanFixedSquareUpperIso f g Q hb ht hl) rfl (Category.id_comp _)

/-- 上側の比較同型は、元の正方形の上二単体の精密化そのものを保持する。 -/
lemma kanFixedSquareUpperIso_heq
    (hl : SSet.yonedaEquiv (prismEndpoint 0 Δ[1] ≫ Q) = (coherentNerveEdge (𝟙 X)).edge) :
    HEq (kanFixedSquareUpperIso f g Q hb ht hl)
      (spaceInfinityTriangleIso (SSet.yonedaEquiv (squareTriangle 0 ≫ Q))) := by
  exact spaceInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _

/-- 下側の比較同型も、元の正方形の下二単体の精密化そのものを保持する。 -/
lemma kanFixedSquareLowerIso_heq
    (hr : SSet.yonedaEquiv (prismEndpoint 1 Δ[1] ≫ Q) = (coherentNerveEdge (𝟙 Y)).edge) :
    HEq (kanFixedSquareLowerIso f g Q hb ht hr)
      (spaceInfinityTriangleIso (SSet.yonedaEquiv (squareTriangle 1 ≫ Q))) := by
  exact spaceInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
