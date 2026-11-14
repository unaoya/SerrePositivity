module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraFrobeniusNaturality

/-!
概要：Frobenius 係数順極限の Čech H⁰ の比較を係数代数の射に自然にする。
方針：filtered 余極限、各段の H⁰、環の順極限の三つの自然性を合成する。
規約：比較後の射は、適合切断の実際の代数写像が誘導する Frobenius 順極限の射。
使われ方：閉厚化の短完全列を同じ Čech H⁰ の四角形へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
universe u
private theorem square_inverse {C : Type*} [Category* C] {X Y X' Y' : C}
    (e : X ≅ X') (d : Y ≅ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : f ≫ d.hom = e.hom ≫ g) : g ≫ d.inv = e.inv ≫ f := by
  apply (cancel_mono d.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι] [Fintype ι]
variable {D E : Finset ι ⥤ CommAlgCat.{u} R} (η : D ⟶ E)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

/-- Čech H⁰ と切断の Frobenius 順極限の比較は、実際の係数代数の射に自然。 -/
theorem algebraCechFrobeniusH0ColimitIso_naturality :
    (fullCechComplexFunctor ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) 0).map
        (colim.map (algebraCechFrobeniusCoefficientNatTrans η p hp hR)) ≫
      (algebraCechFrobeniusH0ColimitIso E p hp hR).hom =
    (algebraCechFrobeniusH0ColimitIso D p hp hR).hom ≫
      ModuleCat.ofHom (frobeniusDirectLimitMap p hp
        (algebraCechEqualizer_primeCast D p hR) (algebraCechEqualizer_primeCast E p hR)
        (fullAlgebraCechEqualizerMap η).toRingHom).toAddMonoidHom.toIntLinearMap := by
  let H : (Finset ι ⥤ ModuleCat.{u} ℤ) ⥤ ModuleCat.{u} ℤ :=
    fullCechComplexFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) 0
  let n := algebraCechFrobeniusCoefficientNatTrans η p hp hR
  let m := frobeniusIntDirectSystemNatTrans p hp
    (algebraCechEqualizer_primeCast D p hR) (algebraCechEqualizer_primeCast E p hR)
    (fullAlgebraCechEqualizerMap η).toRingHom
  have hs := square_inverse (algebraCechFrobeniusH0SystemIso D p hp hR)
    (algebraCechFrobeniusH0SystemIso E p hp hR) m (whiskerRight n H)
    (algebraCechFrobeniusH0SystemIso_naturality η p hp hR)
  have hc : colim.map (whiskerRight n H) ≫
        colim.map (algebraCechFrobeniusH0SystemIso E p hp hR).inv =
      colim.map (algebraCechFrobeniusH0SystemIso D p hp hR).inv ≫ colim.map m := by
    rw [← Functor.map_comp, hs, Functor.map_comp]
  have hr := square_inverse
    (ringDirectLimitIntColimitIso (frobeniusDirectSystemMap (fullAlgebraCechEqualizer D)
      p hp (algebraCechEqualizer_primeCast D p hR)))
    (ringDirectLimitIntColimitIso (frobeniusDirectSystemMap (fullAlgebraCechEqualizer E)
      p hp (algebraCechEqualizer_primeCast E p hR)))
    _ (colim.map m)
    (frobeniusDirectLimitIntColimitIso_naturality p hp
      (algebraCechEqualizer_primeCast D p hR) (algebraCechEqualizer_primeCast E p hR)
      (fullAlgebraCechEqualizerMap η).toRingHom)
  change H.map (colim.map n) ≫ _ = _
  simp only [algebraCechFrobeniusH0ColimitIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, projectiveIntCechSequentialHomologyIso_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (colim.map (whiskerRight n H)), hc]
  simp only [Category.assoc]
  rw [hr]

end SerrePositivity.AlgebraicGeometry
