module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DoubleRightPointCoordinates

/-!
概要：二つの終点を持つ標準 join の前面を、元の全単体の面へ移す。
方針：元の右包含・左包含の計算を二回適用する。
規約：元の同じ面写像を保持。使われ方：追加した実錐の元の前面の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 最後に付けた点を除いた前面は、元の標準単体の最後の面。 -/
lemma doubleRightPointCoordinates_front (n : ℕ) :
    joinInl (join (Δ[n] : SSet.{u}) Δ[0]) Δ[0] ≫ doubleRightPointCoordinates n =
      (joinStdSimplexIso n 0).hom ≫ stdSimplex.map (PinchedHom.front (n + 1)) := by
  rw [doubleRightPointCoordinates, ← Category.assoc, joinInl_joinMap, Category.assoc,
    joinStdSimplexIso_rightPoint_inl]

/-- 元の二つの終点を含めた辺は、同じ標準単体の最終辺になる。 -/
lemma doubleRightPointCoordinates_tail (n : ℕ) :
    joinMap (joinInr (Δ[n] : SSet.{u}) Δ[0]) (𝟙 Δ[0]) ≫ doubleRightPointCoordinates n =
      (joinStdSimplexIso 0 0).hom ≫ stdSimplex.map
        (PinchedHom.extend (PinchedHom.lastVertex n)) := by
  calc
    _ = joinMap (stdSimplex.map (PinchedHom.lastVertex n)) (𝟙 Δ[0]) ≫
        (joinStdSimplexIso (n + 1) 0).hom := by
      rw [doubleRightPointCoordinates, ← Category.assoc, ← joinMap_comp,
        Category.id_comp, joinStdSimplexIso_rightPoint_inr]
    _ = _ := joinStdSimplexIso_rightPoint_naturality _

end SerrePositivity.InfinityCategories.F2
