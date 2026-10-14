module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerComplex

/-! # 可算複体塔の表示同型によるホモトピー逆極限の比較 -/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
variable (R : Type u) [CommRing R]
variable {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}

/-- 各段の同型から、複体の直積の同型を構成する。 -/
def complexTowerProductIso (e : ∀ n, K n ≅ L n) : piObj K ≅ piObj L where
  hom := complexTowerProductMap R (fun n ↦ (e n).hom)
  inv := complexTowerProductMap R (fun n ↦ (e n).inv)
  hom_inv_id := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, complexTowerProductMap_projection]
    rw [← Category.assoc, complexTowerProductMap_projection, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, complexTowerProductMap_projection]
    rw [← Category.assoc, complexTowerProductMap_projection, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- 遷移を保つ各段の同型は、差分写像の矢印の同型を与える。 -/
def complexTowerDifferenceIso (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (e : ∀ n, K n ≅ L n) (he : ∀ n, t n ≫ (e n).hom = (e (n + 1)).hom ≫ s n) :
    Arrow.mk (complexTowerDifference R K t) ≅ Arrow.mk (complexTowerDifference R L s) :=
  Arrow.isoMk (complexTowerProductIso R e) (complexTowerProductIso R e)
    (complexTowerDifference_naturality R t s (fun n ↦ (e n).hom) he)

/-- 遷移を保つ各段の表示同型は、実際のmapping coneとシフトを含む同型を与える。 -/
def complexTowerHomotopyLimitIso
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (e : ∀ n, K n ≅ L n) (he : ∀ n, t n ≫ (e n).hom = (e (n + 1)).hom ≫ s n) :
    complexTowerHomotopyLimit R K t ≅ complexTowerHomotopyLimit R L s :=
  (shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (-1 : ℤ)).mapIso
    (HomologicalComplex.homotopyCofiber.mapArrowIso _ _ (fun j ↦ ⟨j - 1, by simp⟩)
      (complexTowerDifferenceIso R t s e he))

end SerrePositivity.DerivedCompletion
