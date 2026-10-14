module
public import SerrePositivity.PerfectComplex.TensorK0

/-! # Cup products commute with enlargement of support -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory
variable {R : Type u} [CommRing R]
namespace K0WithSupport
variable {Y Y' Z Z' : TopologicalSpace.Closeds (PrimeSpectrum R)}

/-- Enlarge both supports before or after taking the cup product. -/
lemma cup_enlarge (hY : Y ≤ Y') (hZ : Z ≤ Z') (x : K0WithSupport Y) (y : K0WithSupport Z) :
    enlarge (inf_le_inf hY hZ) (cup x y) = cup (enlarge hY x) (enlarge hZ y) := by
  have he :
      (cup (Y := Y) (Z := Z)).compr₂ (enlarge (inf_le_inf hY hZ)) =
        ((cup (Y := Y') (Z := Z')).compl₂ (enlarge hZ)).comp (enlarge hY) := by
    apply cupPairing_hom_ext
    intro X Q
    change enlarge (inf_le_inf hY hZ) (cup (mk Y X) (mk Z Q)) =
      cup (enlarge hY (mk Y X)) (enlarge hZ (mk Z Q))
    simp only [cup_mk_mk, tensorClass, enlarge_mk]
    rfl
  exact DFunLike.congr_fun (DFunLike.congr_fun he x) y

/-- Enlarging just the left support is the corresponding special case. -/
lemma cup_enlarge_left (hY : Y ≤ Y') (x : K0WithSupport Y) (y : K0WithSupport Z) :
    enlarge (inf_le_inf hY (le_refl Z)) (cup x y) = cup (enlarge hY x) y := by
  simpa only [enlarge_refl, AddMonoidHom.id_apply] using cup_enlarge hY (le_refl Z) x y

/-- Enlarging just the right support is the corresponding special case. -/
lemma cup_enlarge_right (hZ : Z ≤ Z') (x : K0WithSupport Y) (y : K0WithSupport Z) :
    enlarge (inf_le_inf (le_refl Y) hZ) (cup x y) = cup x (enlarge hZ y) := by
  simpa only [enlarge_refl, AddMonoidHom.id_apply] using cup_enlarge (le_refl Y) hZ x y
end K0WithSupport
end SerrePositivity
