module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SimplexConeParameter
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.AppendEdgeConeInverse
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SlicePrismSquare
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorNaturalityTriangles

/-!
概要：元の実三角形へ終点を追加し、同じ 012 面を持つ全係数四面体を作る。
方針：同じ右 join prism の三角形と、終点追加の全前面回収を使う。
規約：元の実全面を保持。使われ方：指定四面体比較を元の合成図式へ同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全係数を持つ三角形を、同じ右 join の実錐へ移す。 -/
def triangleRightConeParameter (P : SSet.{u}) :
    Δ[2] ⊗ P ⟶ join (Δ[1] ⊗ P) Δ[0] :=
  (squareTriangle 0 ▷ P) ≫ (α_ (Δ[1] : SSet.{u}) Δ[1] P).hom ≫
    rightMappingSpacePrism (Δ[1] ⊗ P)

/-- 元の slice prism の三角形は、同じ全錐への係数付き制限そのもの。 -/
lemma triangleRightConeParameter_comp {X P : SSet.{u}} (z : X _⦋0⦌)
    (R : Δ[1] ⊗ P ⟶ sliceOver (SSet.yonedaEquiv.symm z)) :
    triangleRightConeParameter P ≫ sliceOverUncurry R =
      squarePrismTriangle (slicePrismSquare z R) 0 := by
  simp only [triangleRightConeParameter, squarePrismTriangle, slicePrismSquare, Category.assoc]

/-- 元の同じ三角形へ終点を追加する、全係数付き四面体の比較射。 -/
def coneTetrahedronParameter (P : SSet.{u}) :
    Δ[3] ⊗ P ⟶ join (Δ[1] ⊗ P) Δ[1] :=
  simplexConeParameter 2 P ≫ joinMap (triangleRightConeParameter P) (𝟙 Δ[0]) ≫
    appendEdgeConeCoordinatesInverse (Δ[1] ⊗ P)

/-- 同じ四面体の元の前面は、実終辺の始点上の同じ実三角形。 -/
lemma coneTetrahedronParameter_front (P : SSet.{u}) :
    (stdSimplex.δ (3 : Fin 4) ▷ P) ≫ coneTetrahedronParameter P =
      triangleRightConeParameter P ≫ joinMap (𝟙 (Δ[1] ⊗ P)) (stdSimplex.δ (1 : Fin 2)) := by
  have hf : (stdSimplex.δ (3 : Fin 4) ▷ P) ≫ simplexConeParameter 2 P =
      joinInl (Δ[2] ⊗ P) Δ[0] := by
    simpa only [PinchedHom.front_eq_δ, CosimplicialObject.δ,
      show Fin.last (2 + 1) = (3 : Fin 4) from by decide] using simplexConeParameter_front 2 P
  rw [coneTetrahedronParameter, ← Category.assoc, hf, ← Category.assoc, joinInl_joinMap,
    Category.assoc, appendEdgeConeCoordinatesInverse_front]

end SerrePositivity.InfinityCategories.F2
