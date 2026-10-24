module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofCellRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathOperations

/-!
概要：同じ切断を持つ二射を、切断の実右逆 roof の指定経路から比較する。
方針：同じ右経路を二射で写し、一方を反転して二重 cell 細分で合成する。
規約：右逆 roof の存在は結論に含めない。使われ方：対角射の右逆による経路反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A P Q : Mon (Complex R)}
  (s : A ⟶ P) (l r : P ⟶ A) (hl : s ≫ l = 𝟙 A) (hr : s ≫ r = 𝟙 A)
  (q : SurjectiveRoof R Q A) (t : Q ⟶ P)
  (w : Path.Witness R (q.numerator ≫ s) (q.denominator ≫ t))

def SurjectiveRoof.diagonalCancellation : Path.Witness R
    ((q.cellRefinement R 2).denominator ≫ (t ≫ l))
    ((q.cellRefinement R 2).denominator ≫ (t ≫ r)) := by
  let wl := w.postcomp l
  let wr := w.postcomp r
  let vl : Path.Witness R q.numerator (q.denominator ≫ (t ≫ l)) :=
    ⟨wl.hom, by simpa only [Category.assoc, hl, Category.comp_id] using wl.source_eq,
      wl.target_eq.trans (Category.assoc _ _ _)⟩
  let vr : Path.Witness R q.numerator (q.denominator ≫ (t ≫ r)) :=
    ⟨wr.hom, by simpa only [Category.assoc, hr, Category.comp_id] using wr.source_eq,
      wr.target_eq.trans (Category.assoc _ _ _)⟩
  let v := (vl.cellReverse R).cellComp R
    (vr.precomp (cellAugmentation R q.apex))
  exact { hom := v.hom
          source_eq := by
            simpa only [SurjectiveRoof.cellRefinement, iteratedCellAugmentation,
              iteratedCellResolution, Category.assoc, Category.comp_id] using v.source_eq
          target_eq := by
            simpa only [SurjectiveRoof.cellRefinement, iteratedCellAugmentation,
              iteratedCellResolution, Category.assoc, Category.comp_id] using v.target_eq }

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
