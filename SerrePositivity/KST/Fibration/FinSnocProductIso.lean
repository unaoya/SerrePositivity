module
public import SerrePositivity.KST.Fibration.WeakStringFiniteComparison

/-! # 終端の一因子を取り出す元の有限積の同型 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Fibration

/-- 全ての元の積射影を保つ、先行有限積と最後の一因子への同型。 -/
def finSnocProductIso (X : SSet.{u}) (n : ℕ) :
    (∏ᶜ fun _ : Fin (n + 1) => X) ≅ (∏ᶜ fun _ : Fin n => X) ⊗ X where
  hom := lift (Pi.lift (fun i : Fin n => Pi.π (fun _ : Fin (n + 1) => X) i.castSucc))
    (Pi.π (fun _ : Fin (n + 1) => X) (Fin.last n))
  inv := Pi.lift (fun i => Fin.lastCases (snd _ X)
    (fun j => fst _ X ≫ Pi.π (fun _ : Fin n => X) j) i)
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    rw [Category.assoc, Pi.lift_comp_π, Category.id_comp]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.lastCases_last]
      change lift _ _ ≫ snd _ X = _
      exact lift_snd _ _
    · rw [Fin.lastCases_castSucc]
      change lift _ _ ≫ (fst _ X ≫ Pi.π _ j) = _
      rw [lift_fst_assoc, Pi.lift_comp_π]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.id_comp]
      apply Pi.hom_ext
      intro i
      rw [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π]
      rw [Fin.lastCases_castSucc]
    · rw [Category.assoc, lift_snd, Pi.lift_comp_π, Category.id_comp]
      rw [Fin.lastCases_last]

/-- 同じ有限積の射対から、元の先行射影群と最後の射影を回収する。 -/
lemma finSnocProductIso_lift {P X : SSet.{u}} (n : ℕ) (f : Fin (n + 1) → (P ⟶ X)) :
    Pi.lift f ≫ (finSnocProductIso X n).hom =
      lift (Pi.lift (fun i : Fin n => f i.castSucc)) (f (Fin.last n)) := by
  change Pi.lift f ≫ lift _ _ = _
  rw [comp_lift, Pi.lift_comp_π]
  apply congrArg₂ lift
  · apply Pi.hom_ext
    intro i
    rw [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π, Pi.lift_comp_π]
  · rfl

end SerrePositivity.KST.Fibration
