module
public import SerrePositivity.KST.Fibration.WeakStringFiniteComparison

/-! # 元の Fin 2 添字積と二項積の射影を保つ同型 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Fibration

/-- 二つの元の射影を指定した、定値 Fin 2 積と二項積の同型。 -/
def finTwoProductIso (X : SSet.{u}) : (∏ᶜ fun _ : Fin 2 => X) ≅ X ⊗ X where
  hom := lift (Pi.π (fun _ : Fin 2 => X) 0) (Pi.π (fun _ : Fin 2 => X) 1)
  inv := Pi.lift (fun i => Fin.cases (fst X X) (fun _ => snd X X) i)
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    rw [Category.assoc, Pi.lift_comp_π, Category.id_comp]
    fin_cases i
    · change lift _ _ ≫ fst X X = _
      exact lift_fst _ _
    · change lift _ _ ≫ snd X X = _
      exact lift_snd _ _
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Pi.lift_comp_π, Category.id_comp]
      rfl
    · rw [Category.assoc, lift_snd, Pi.lift_comp_π, Category.id_comp]
      rfl

/-- 同型は全 Fin 2 成分を、元の二項射対へ送る。 -/
lemma finTwoProductIso_lift {P X : SSet.{u}} (f : Fin 2 → (P ⟶ X)) :
    Pi.lift f ≫ (finTwoProductIso X).hom = lift (f 0) (f 1) := by
  change Pi.lift f ≫ lift _ _ = _
  rw [comp_lift, Pi.lift_comp_π, Pi.lift_comp_π]

end SerrePositivity.KST.Fibration
