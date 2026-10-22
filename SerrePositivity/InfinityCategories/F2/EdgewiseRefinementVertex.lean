module

public import SerrePositivity.InfinityCategories.F2.EdgewiseOneFaceCoordinates
public import SerrePositivity.InfinityCategories.F2.EdgewiseRefinementResolutions

/-!
概要：元の一単体を共通解像の実頂点に入れ、一次元係数の両面を計算する。
方針：重みの実両面の座標式と Yoneda の自然性を合成する。
規約：元の一単体と実際の重みの射を保持する。
使われ方：左右精密化の共通解像の二辺が同じ実終点を持つことの同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の一単体を、その同じ重みからの射として共通解像の頂点に保持する。 -/
def edgewiseRefinementVertex {X : SSet.{u}} (e : X _⦋1⦌) :
    (edgewiseSubdivision X) _⦋0⦌ :=
  (edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm e

/-- 標準三単体の係数を持つ実共通解像の辺の両面は同じ係数の二頂点制限。 -/
lemma edgewiseRefinementStandard_face {X : SSet.{u}} (e : X _⦋1⦌)
    (β : ⦋3⦌ ⟶ ⦋1⦌) (i : Fin 2) :
    (edgewiseSubdivision X).δ i
      ((edgewiseWeightIso 1).hom ≫ stdSimplex.map β ≫ SSet.yonedaEquiv.symm e) =
      edgewiseRefinementVertex
        (X.map (SimplexCategory.mkHom (edgewiseOneFaceInclusion i) ≫ β).op e) := by
  change edgewiseWeight.map (SimplexCategory.δ i) ≫
    (edgewiseWeightIso 1).hom ≫ stdSimplex.map β ≫ SSet.yonedaEquiv.symm e = _
  rw [← Category.assoc (edgewiseWeight.map _), edgewiseWeight_one_face,
    Category.assoc, ← Category.assoc (stdSimplex.map _), ← stdSimplex.map_comp,
    SSet.yonedaEquiv_symm_naturality_left]
  rfl

end SerrePositivity.InfinityCategories.F2
