module
public import SerrePositivity.DifferentialGraded.Bimodule.Basic

/-! # bimoduleの二つの作用による外延性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 両因子での制限が一致すれば、主Hom endを持つbimoduleも一致する。 -/
lemma ext_rightAt_leftAt (M N : Bimodule A B C)
    (hr : ∀ c, M.rightAt c = N.rightAt c) (hl : ∀ b, M.leftAt b = N.leftAt b) : M = N := by
  rcases M with ⟨Mo, Mm, Mi, Mc⟩
  rcases N with ⟨No, Nm, Ni, Nc⟩
  have ho : Mo = No := funext hr
  subst No
  apply EnrichedFunctor.ext (Complex A) (C := C) (D := RightModule A B)
    (F := ⟨Mo, Mm, Mi, Mc⟩) (G := ⟨Mo, Nm, Ni, Nc⟩) (fun _ => rfl)
  intro c d
  rw [eqToHom_refl, Category.comp_id]
  apply moduleHom_ext
  intro b
  have hmap (F G : LeftModule A C) (h : F = G) : HEq (F.map c d) (G.map c d) := by
    cases h
    rfl
  exact eq_of_heq (hmap _ _ (hl b))

end SerrePositivity.DifferentialGraded.Bimodule
