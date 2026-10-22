module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridSquareIndex
public import SerrePositivity.InfinityCategories.Stable.PosetProductNerveIso

/-!
概要：任意の四角形を厳密に保つ比較格子と二段階の局所余極限を構成する。
方針：有限順序添字の厳密左 Kan 拡張と、指定終対象への延長を交互に使う。
規約：各面の押し出し性はまだ結論しない。使われ方：HA 1.4.2.15 の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
def excisionGridSquareShapeIso : nerve ExcisionGridSquareIndex.{u} ≅
    (Δ[1] : SSet.{u}) ⊗ Δ[1] :=
  PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (α := PartOrd.of ExcisionGridSquareIndex.{u})
      (β := PartOrd.of (ULift.{u} (Fin 2) × ULift.{u} (Fin 2)))
      excisionGridSquareOrderIso) ≪≫
    posetProductSwapNerveIso (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) ≪≫
      MonoidalCategory.tensorIso (stdSimplex.isoNerve 1).symm (stdSimplex.isoNerve 1).symm

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
abbrev excisionGridSquareInclusion :
    ExcisionGridSquareIndex.{u} ⥤ ExcisionGridSeedIndex.{u} :=
  posetSubtypeInclusion IsExcisionGridSquare

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma excisionGridSquareShapeIso_vertex (i j : Fin 2) :
    excisionGridSquareShapeIso.hom.app (Opposite.op ⦋0⦌)
      (nerveVertex (excisionGridSquarePoint.{u} i j)) =
        (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) := by
  apply Prod.ext <;> apply stdSimplex.ext <;> intro k <;> rfl

end SerrePositivity.InfinityCategories
