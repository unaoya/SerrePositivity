module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathOperations
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraIteratedCellResolution

/-!
概要：同じ終点に至る二組の実乗法的経路を、有限 cell 細分上で比較する。
方針：各組を cell 合成し、一方を反転して同じ二重 cell 源上に揃える。
規約：一般代数への経路を元の源上で合成しない。使われ方：実 roof の右三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {T E : Mon (Complex R)}
  {a b c x y : T ⟶ E}

def Path.Witness.cellComparePairs (v : Path.Witness R a b) (w : Path.Witness R b c)
    (s : Path.Witness R x y) (t : Path.Witness R y c) :
    Path.Witness R (iteratedCellAugmentation R T 3 ≫ a)
      (iteratedCellAugmentation R T 3 ≫ x) := by
  let vw := v.cellComp R w
  let st := (s.cellComp R t).cellReverse R
  let h := (vw.precomp (cellAugmentation R (cellResolution R T))).cellComp R st
  exact { hom := h.hom
          source_eq := by
            simpa only [iteratedCellAugmentation, iteratedCellResolution,
              Category.assoc, Category.comp_id] using h.source_eq
          target_eq := by
            simpa only [iteratedCellAugmentation, iteratedCellResolution,
              Category.assoc, Category.comp_id] using h.target_eq }

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
