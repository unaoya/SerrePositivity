module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DoubleRightPointCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceRightKan

/-!
概要：二重終点の中間を除く全面を、元の標準単体の対応する面へ移す。
方針：標準 join 同型の自然性と元の最終点固定面を使う。
規約：同じ面写像を保持。使われ方：追加錐の後合成面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の二重錐の中間終点を除く全面は、元の標準単体の最終手前の面。 -/
lemma doubleRightPointCoordinates_middle (n : ℕ) :
    joinMap (joinInl (Δ[n] : SSet.{u}) Δ[0]) (𝟙 Δ[0]) ≫ doubleRightPointCoordinates n =
      (joinStdSimplexIso n 0).hom ≫
        stdSimplex.map (SimplexCategory.δ (Fin.last (n + 1)).castSucc) := by
  rw [doubleRightPointCoordinates, ← Category.assoc, ← joinMap_comp, Category.id_comp,
    joinStdSimplexIso_rightPoint_inl, joinStdSimplexIso_rightPoint_naturality,
    PinchedHom.front_eq_δ, pinchedExtend_δ]

end SerrePositivity.InfinityCategories.F2
