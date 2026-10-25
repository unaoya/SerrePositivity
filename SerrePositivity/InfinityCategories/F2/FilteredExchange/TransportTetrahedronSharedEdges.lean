module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTetrahedronDiagram

/-!
概要：同じ実四面体の六本の共有辺を、面の実 prism として照合する。
方針：元の二重面関係を六通りに特殊化する。
規約：実辺を選び直さない。使われ方：四面に現れる指定区間比較の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} {v : Fin 4 → B _⦋0⦌}
  {f : ∀ i, P ⟶ vertexFiber p (v i)} (D : TransportTetrahedronDiagram p v f)

/-- 元の実辺 01 は両面で同じ全係数の prism。 -/
lemma TransportTetrahedronDiagram.shared_edge01 :
    (D.face 2).diagram.bottomPrism = (D.face 3).diagram.bottomPrism := by
  rw [D.face_bottomPrism, D.face_bottomPrism]
  exact simplexSharedFacePrism D.simplex 2 2 (by decide)

/-- 元の実辺 02 は両面で同じ全係数の prism。 -/
lemma TransportTetrahedronDiagram.shared_edge02 :
    (D.face 1).diagram.bottomPrism = (D.face 3).diagram.leftPrism := by
  rw [D.face_bottomPrism, D.face_leftPrism]
  exact simplexSharedFacePrism D.simplex 1 2 (by decide)

/-- 元の実辺 03 は両面で同じ全係数の prism。 -/
lemma TransportTetrahedronDiagram.shared_edge03 :
    (D.face 1).diagram.leftPrism = (D.face 2).diagram.leftPrism := by
  rw [D.face_leftPrism, D.face_leftPrism]
  exact simplexSharedFacePrism D.simplex 1 1 (by decide)

/-- 元の実辺 12 は両面で同じ全係数の prism。 -/
lemma TransportTetrahedronDiagram.shared_edge12 :
    (D.face 0).diagram.bottomPrism = (D.face 3).diagram.rightPrism := by
  rw [D.face_bottomPrism, D.face_rightPrism]
  exact simplexSharedFacePrism D.simplex 0 2 (by decide)

/-- 元の実辺 13 は両面で同じ全係数の prism。 -/
lemma TransportTetrahedronDiagram.shared_edge13 :
    (D.face 0).diagram.leftPrism = (D.face 2).diagram.rightPrism := by
  rw [D.face_leftPrism, D.face_rightPrism]
  exact simplexSharedFacePrism D.simplex 0 1 (by decide)

/-- 元の実辺 23 は両面で同じ全係数の prism。 -/
lemma TransportTetrahedronDiagram.shared_edge23 :
    (D.face 0).diagram.rightPrism = (D.face 1).diagram.rightPrism := by
  rw [D.face_rightPrism, D.face_rightPrism]
  exact simplexSharedFacePrism D.simplex 0 0 (by decide)

end SerrePositivity.InfinityCategories.F2
