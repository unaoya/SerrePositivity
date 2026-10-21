module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolutionLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolutionMap

/-!
概要：任意の底の代数射を、全射準同型を通る cell 分解上の実射へ持ち上げる。
方針：元の cell 比較と全段の増大持ち上げを合成し、元の底の射との厳密な式を保つ。
規約：cell 比較の未提供の関手則は使わない。使われ方：代数の導来写像比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)} (f : A ⟶ B) (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)

def cellResolutionMapLift : cellResolution R A ⟶ C :=
  cellResolutionMap R f ≫ cellResolutionLift R p hs hq

lemma cellResolutionMapLift_projection :
    cellResolutionMapLift R f p hs hq ≫ p = cellAugmentation R A ≫ f := by
  rw [cellResolutionMapLift, Category.assoc, cellResolutionLift_projection,
    cellResolutionMap_augmentation]

lemma cellResolutionMapLift_quasiIso (hf : QuasiIso f.hom) :
    QuasiIso (cellResolutionMapLift R f p hs hq).hom :=
  quasiIso_comp _ _ (hφ := cellResolutionMap_quasiIso R f hf)
    (hφ' := cellResolutionLift_quasiIso R p hs hq)

include hs hq in
lemma exists_cellResolutionMapLift :
    ∃ g : cellResolution R A ⟶ C, g ≫ p = cellAugmentation R A ≫ f :=
  ⟨cellResolutionMapLift R f p hs hq, cellResolutionMapLift_projection R f p hs hq⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
