module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerIso
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerProjection
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleConeNaturality

/-! # 複体塔の表示同型と標準射影の自然性 -/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]
variable {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (e : ∀ n, K n ≅ L n) (he : ∀ n, t n ≫ (e n).hom = (e (n + 1)).hom ≫ s n)

/-- 標準射影の零次数成分は、外側の錐の第1射影。 -/
theorem complexTowerProjection_fst_zero :
    (complexTowerProjection R K t).f 0 =
      fstX (complexTowerDifference R K t) (-1) 0 (by decide) := by
  simp [complexTowerProjection, CochainComplex.mappingCocone.fst,
    CochainComplex.HomComplex.Cochain.leftShift, CochainComplex.shiftFunctorObjXIso,
    CochainComplex.mappingCone.fst]

/-- 塔の比較は、外側の錐の零次数の第1射影を保つ。 -/
theorem complexTowerHomotopyLimitIso_fst_zero :
    (complexTowerHomotopyLimitIso R t s e he).hom.f 0 ≫
      fstX (complexTowerDifference R L s) (-1) 0 (by decide) =
    fstX (complexTowerDifference R K t) (-1) 0 (by decide) ≫
      (complexTowerProductIso R e).hom.f 0 := by
  change (mapArrowHom (complexTowerDifference R K t) (complexTowerDifference R L s)
    (fun j ↦ ⟨j - 1, by simp⟩) (complexTowerDifferenceIso R t s e he).hom).f (-1) ≫ _ = _
  exact moduleConeArrowMap_fst _ _ _ (-1) 0 (by decide)

/-- 塔の比較は、外側の錐の零次数の第2射影を保つ。 -/
theorem complexTowerHomotopyLimitIso_snd_zero :
    (complexTowerHomotopyLimitIso R t s e he).hom.f 0 ≫
      sndX (complexTowerDifference R L s) (-1) =
    sndX (complexTowerDifference R K t) (-1) ≫ (complexTowerProductIso R e).hom.f (-1) := by
  change (mapArrowHom (complexTowerDifference R K t) (complexTowerDifference R L s)
    (fun j ↦ ⟨j - 1, by simp⟩) (complexTowerDifferenceIso R t s e he).hom).f (-1) ≫ _ = _
  exact moduleConeArrowMap_snd _ _ _ (-1)

end SerrePositivity.DerivedCompletion
