module
public import SerrePositivity.KST.SConstruction.ZeroRowPathFiberComparison

/-! # 経路零行の退化と定数経路切断の一致
概要：元の零段の退化を経路の零列へ入れると、既存の定数経路切断そのものになる。
方針：先頭追加後の零段への作用素の一意性で全単体の等号を証明する。
規約：chosen zero を要求しない。使われ方：零行の fiber 比較の基点の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 零段の退化と経路の零列の合成は定数経路切断に厳密に一致する。 -/
lemma simplicialPathZeroColumn_section (D : SimplicialObject SSet.{u}) :
    D.map (SimplexCategory.σ (0 : Fin 1)).op ≫ diagonalZeroColumn (simplicialPath D) =
      simplicialPathDiagonalSection D := by
  apply NatTrans.ext
  funext d
  change (D.map (SimplexCategory.σ (0 : Fin 1)).op ≫
    D.map (SimplexPrefix.functor.map (SimplexCategory.const d.unop ⦋0⦌ 0)).op).app d = _
  rw [← D.map_comp, ← op_comp]
  have he : SimplexPrefix.functor.map (SimplexCategory.const d.unop ⦋0⦌ 0) ≫
      SimplexCategory.σ (0 : Fin 1) =
    SimplexCategory.isTerminalZero.from (SimplexPrefix.functor.obj d.unop) := Subsingleton.elim _ _
  rw [he]
  rfl

/-- 元の零段の退化の零行評価は既存の点つき Kan 経路の基点に厳密に定数。 -/
lemma zeroRowPathToKan_degeneracy (r : ℕ) (X : StableModel.{u}) :
    (iteratedSRealizationDiagram r X).map (SimplexCategory.σ (0 : Fin 1)).op ≫
        zeroRowPathToKan r X =
      toUnit ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
        ((pointedIteratedPathKanFunctor r).obj X).hom := by
  let D := iteratedSRealizationDiagram r X
  have he : D.map (SimplexCategory.σ (0 : Fin 1)).op ≫
      diagonalZeroColumn (iteratedPathRealizationDiagram r X) =
    simplicialPathDiagonalSection D := simplicialPathZeroColumn_section D
  have hq : simplicialPathDiagonalSection D ≫ pointedIteratedPathQuotient r X =
    toUnit (D.obj (Opposite.op ⦋0⦌)) ≫ (pointedIteratedPathRealization r X).hom :=
    PointedObject.cofiberQuotient_condition _
  have hu : (pointedIteratedPathRealization r X).hom ≫
      (Spectra.PointedKanReplacement.unit.app (pointedIteratedPathRealization r X)).right =
    ((pointedIteratedPathKanFunctor r).obj X).hom :=
    Under.w (Spectra.PointedKanReplacement.unit.app (pointedIteratedPathRealization r X))
  change D.map (SimplexCategory.σ (0 : Fin 1)).op ≫
    (diagonalZeroColumn (iteratedPathRealizationDiagram r X) ≫
      (pointedIteratedPathQuotient r X ≫
        (Spectra.PointedKanReplacement.unit.app (pointedIteratedPathRealization r X)).right)) = _
  rw [← Category.assoc, he, ← Category.assoc, hq, Category.assoc, hu]

end SerrePositivity.KST.SConstruction
