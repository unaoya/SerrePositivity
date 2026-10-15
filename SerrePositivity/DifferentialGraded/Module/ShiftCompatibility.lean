module
public import SerrePositivity.DifferentialGraded.Module.ShiftHomotopy

/-! # 商shiftの加法性と評価でのshift交換同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleHomotopyShiftAdditive (s : ℤ) :
    (shiftFunctor (ModuleHomotopyCategory A D) s).Additive := by
  let Q := moduleToHomotopy A D
  let : (Q ⋙ shiftFunctor (ModuleHomotopyCategory A D) s).Additive :=
    Functor.additive_of_iso (Q.commShiftIso s)
  exact Functor.additive_of_full_essSurj_comp Q _

lemma moduleEvaluation_shiftComm (M : ModuleCategory A D) (s t : ℤ) (x : D) :
    (moduleEvaluation A D x).map
      ((shiftFunctorComm (ModuleCategory A D) s t).hom.app M) =
        (shiftFunctorComm (Complex A) s t).hom.app ((moduleEvaluation A D x).obj M) := by
  have h := (moduleEvaluation A D x).map_shiftFunctorComm_hom_app M s t
  change (moduleEvaluation A D x).map
    ((shiftFunctorComm (ModuleCategory A D) s t).hom.app M) =
      𝟙 _ ≫ (𝟙 _)⟦t⟧' ≫
        (shiftFunctorComm (Complex A) s t).hom.app ((moduleEvaluation A D x).obj M) ≫
          (𝟙 _)⟦s⟧' ≫ 𝟙 _ at h
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at h
  exact h.trans (Category.comp_id _)

end SerrePositivity.DifferentialGraded
