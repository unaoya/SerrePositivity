module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraFrobeniusH0Inclusions

/-!
概要：Frobenius 系の各段の適合切断の Čech H⁰ の像を元の式で表示する。
方針：標準写像の比較に有限段の H⁰ の同型を代入する。
規約：比較先の元は既存の FrobeniusDirectLimit の標準写像である。
使われ方：基底のスカラー切断を実際の Čech 増大写像と同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι] [Fintype ι]
variable (D : Finset ι ⥤ CommAlgCat.{u} R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

/-- 各段の適合切断の Čech H⁰ の像は、同じ段の Frobenius 順極限の元となる。 -/
theorem algebraCechFrobeniusH0ColimitIso_stage (n : ℕ)
    (s : fullAlgebraCechEqualizer D) :
    (algebraCechFrobeniusH0ColimitIso D p hp hR).hom.hom
      (((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) 0).map
        (fullCechComplexMap
          (colimit.ι (algebraCechFrobeniusCoefficientFunctor D p hp hR) n))).hom
        (fullAlgebraCechIntH0Equiv D s)) =
      frobeniusDirectLimitOf (fullAlgebraCechEqualizer D) p hp
        (algebraCechEqualizer_primeCast D p hR) n s := by
  have h := congrArg (fun f ↦ f.hom (fullAlgebraCechIntH0Equiv D s))
    (algebraCechFrobeniusH0ColimitIso_ι D p hp hR n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  have hs : ((algebraCechFrobeniusH0SystemIso D p hp hR).app n).inv.hom
      (fullAlgebraCechIntH0Equiv D s) = s :=
    (fullAlgebraCechIntH0Equiv D).symm_apply_apply s
  let f := frobeniusDirectSystemMap (fullAlgebraCechEqualizer D) p hp
    (algebraCechEqualizer_primeCast D p hR)
  let e := ringDirectLimitIntColimitIso f
  let t := colimit.ι (linearDirectSystemFunctor (ringDirectSystemIntMap f)) n
  have he : e.inv.hom (t.hom s) =
      frobeniusDirectLimitOf (fullAlgebraCechEqualizer D) p hp
        (algebraCechEqualizer_primeCast D p hR) n s :=
    (congrArg (fun x ↦ e.inv.hom x) (ringDirectLimitIntColimitIso_of f n s).symm).trans
      (e.toLinearEquiv.symm_apply_apply _)
  exact h.trans ((congrArg (fun x ↦ e.inv.hom (t.hom x)) hs).trans he)

/-- 同じ標準写像の公式を比較の逆向きに述べたもの。 -/
theorem algebraCechFrobeniusH0ColimitIso_inv_of (n : ℕ)
    (s : fullAlgebraCechEqualizer D) :
    (algebraCechFrobeniusH0ColimitIso D p hp hR).inv.hom
      (frobeniusDirectLimitOf (fullAlgebraCechEqualizer D) p hp
        (algebraCechEqualizer_primeCast D p hR) n s) =
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) 0).map
        (fullCechComplexMap
          (colimit.ι (algebraCechFrobeniusCoefficientFunctor D p hp hR) n))).hom
        (fullAlgebraCechIntH0Equiv D s) := by
  let e := (algebraCechFrobeniusH0ColimitIso D p hp hR).toLinearEquiv
  exact (congrArg (fun x ↦ e.symm x)
    (algebraCechFrobeniusH0ColimitIso_stage D p hp hR n s)).symm.trans
      (e.symm_apply_apply _)

end SerrePositivity.AlgebraicGeometry
