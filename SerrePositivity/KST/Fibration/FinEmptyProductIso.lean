module
public import SerrePositivity.KST.Fibration.WeakStringFiniteComparison

/-! # 空の cofiber 群を持つ元の有限積の同型 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Fibration

/-- 空の有限積因子を除く同型。順射は元の第一射影そのもの。 -/
def finEmptyProductIso (X Y : SSet.{u}) : X ⊗ (∏ᶜ fun _ : Fin 0 => Y) ≅ X where
  hom := fst _ _
  inv := lift (𝟙 X) (Pi.lift (fun i => Fin.elim0 i))
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.comp_id, Category.id_comp]
    · apply Pi.hom_ext
      intro i
      exact Fin.elim0 i
  inv_hom_id := lift_fst _ _

end SerrePositivity.KST.Fibration
