module
public import SerrePositivity.DifferentialGraded.Module.ShiftHomotopyComparison
public import SerrePositivity.DifferentialGraded.Category.QuotientComparison

/-! # dg加群shiftの商比較を実際の閉零代表で評価する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商比較の抽象的な評価式を使い、全Hom shiftのH⁰比較を元の商shiftの成分に戻す。 -/
lemma moduleShiftDGHomotopyIso_closed_hom_app (s : ℤ) (M : ModuleCategory A D) :
    (moduleShiftDGHomotopyIso A D s).hom.app ((moduleToHomotopy A D).obj M) =
      ((moduleToHomotopy A D).commShiftIso s).hom.app M := by
  have h := quotientComparison_hom_app (boundaryRelation A (RightModule A D))
    (moduleShiftDG A D s).onHomotopy (shiftFunctor (ModuleHomotopyCategory A D) s)
    (moduleShiftDG A D s).onClosed (moduleShiftFunctor A D s) (moduleToHomotopy A D)
    (moduleShiftDG A D s).onHomotopy_fac (moduleShiftDG_onClosed_eq A D s)
    ((moduleToHomotopy A D).commShiftIso s) M
  have h' : (moduleShiftDGHomotopyIso A D s).hom.app ((moduleToHomotopy A D).obj M) =
      𝟙 ((moduleToHomotopy A D).obj (M⟦s⟧)) ≫
        (moduleToHomotopy A D).map (𝟙 (M⟦s⟧)) ≫
          ((moduleToHomotopy A D).commShiftIso s).hom.app M := h
  let f := ((moduleToHomotopy A D).commShiftIso s).hom.app M
  have hi := (moduleToHomotopy A D).map_id (M⟦s⟧)
  exact h'.trans ((Category.id_comp _).trans
    ((congrArg (fun g => g ≫ f) hi).trans (Category.id_comp f)))

end SerrePositivity.DifferentialGraded
