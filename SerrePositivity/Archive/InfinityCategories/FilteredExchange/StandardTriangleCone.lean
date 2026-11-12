module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorNaturalityTriangles
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePrisms
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice

/-!
概要：元の標準三角形の右 prism は、同じ標準 join 座標の逆そのもの。
方針：標準 join 同型の後で普遍二単体の三頂点を計算する。
規約：全単体の射の等式。使われ方：全係数付き三角形錐の一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の零番三角形の右 prism は、同じ三角形の標準錐への逆座標。 -/
lemma squareTriangle_rightMappingSpacePrism :
    squareTriangle.{u} 0 ≫ rightMappingSpacePrism Δ[1] = (joinStdSimplexIso 1 0).inv := by
  apply (cancel_mono (joinStdSimplexIso 1 0).hom).1
  rw [Category.assoc, Iso.inv_hom_id]
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> decide

end SerrePositivity.InfinityCategories.F2
