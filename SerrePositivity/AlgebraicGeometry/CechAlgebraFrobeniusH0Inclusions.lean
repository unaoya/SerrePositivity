module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraFrobeniusH0
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntSequentialInclusions

/-!
概要：Frobenius 系の各段の Čech H⁰ を適合切断環の順極限の標準写像と照合する。
方針：Čech H の順極限比較、図式の同型、環の順極限比較の標準写像の公式を合成。
規約：既存の algebraCechFrobeniusH0ColimitIso を用いる。
使われ方：実際の増大写像と H⁰ の短完全列の写像の一致。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι] [Fintype ι]
variable (D : Finset ι ⥤ CommAlgCat.{u} R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

/-- Čech H⁰ 比較に各有限段から入る射を、切断環の系の標準写像で表示する。 -/
theorem algebraCechFrobeniusH0ColimitIso_ι (n : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) 0).map
        (fullCechComplexMap
          (colimit.ι (algebraCechFrobeniusCoefficientFunctor D p hp hR) n)) ≫
      (algebraCechFrobeniusH0ColimitIso D p hp hR).hom =
    ((algebraCechFrobeniusH0SystemIso D p hp hR).app n).inv ≫
      colimit.ι (linearDirectSystemFunctor (ringDirectSystemIntMap
        (frobeniusDirectSystemMap (fullAlgebraCechEqualizer D) p hp
          (algebraCechEqualizer_primeCast D p hR)))) n ≫
      (ringDirectLimitIntColimitIso
        (frobeniusDirectSystemMap (fullAlgebraCechEqualizer D) p hp
          (algebraCechEqualizer_primeCast D p hR))).inv := by
  simp only [algebraCechFrobeniusH0ColimitIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, projectiveIntCechSequentialHomologyIso_ι]
  rw [colimit.ι_map_assoc]
  rfl

end SerrePositivity.AlgebraicGeometry
