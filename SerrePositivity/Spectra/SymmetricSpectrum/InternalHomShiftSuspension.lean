module

public import SerrePositivity.Spectra.General.ShiftedHomSuspension
public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHomShiftStructure
public import SerrePositivity.Spectra.SymmetricSpectrum.Suspension

/-! # 円周を座標とする懸垂の添字表示 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level structureMap)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 値域の懸垂とブロック交換を、第一球面の構造射と次数移送で表示する。 -/
lemma suspensionMap_shiftedIndex (n q : ℕ) (E : SymmetricSpectrum.{u}) :
    suspensionMap E (n + q) ≫ E.X.map (GeneralSymmetricSpectrum.shiftedHomSuspensionIndex n q) =
      (spherePowerOneIso.{u}).inv ▷ level E (n + q) ≫
        structureMap E 1 (n + q) ≫ E.X.map (GeneralSymmetricSpectrum.shiftedHomStructureIndex n 1 q) ≫
          eqToHom (congrArg (level E) (congrArg (n + ·) (Nat.one_add q))) := by
  unfold suspensionMap GeneralSymmetricSpectrum.shiftedHomSuspensionIndex
  erw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  erw [eqToHom_map, eqToHom_map]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rfl

end SerrePositivity.SymmetricSpectrum
