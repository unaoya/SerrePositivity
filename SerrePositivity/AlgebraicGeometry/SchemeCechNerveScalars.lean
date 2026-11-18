module

public import SerrePositivity.AlgebraicGeometry.SchemeScalarMorphism
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicTopology.CechNerve

/-!
概要：基底への実際の射を保つ引き戻しは、大域スカラーと標数を保つ。
方針：Γ–Spec の自然性と、同じ nerve の増大射の自然性を使う。
規約：全ての開の標数を元の基底環から供給する。
使われ方：同じタプル被覆の係数関手への増大写像。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- 基底への同じ射を保つ写像は、その大域スカラーを保つ。 -/
theorem schemeScalarHom_over {X Y : Scheme.{u}} (v : X ⟶ Y)
    (iY : Y ⟶ Spec (CommRingCat.of R)) (iX : X ⟶ Spec (CommRingCat.of R))
    (he : v ≫ iY = iX) :
    schemeScalarHom X iX = v.appTop.hom.comp (schemeScalarHom Y iY) := by
  have h := schemeScalarHom_naturality Y v iY iX (RingHom.id R) (by simpa using he)
  simpa only [RingHom.comp_id] using h

/-- 基底の p の零化は、同じ構造射を持つ全ての開の切断環に移る。 -/
theorem schemeScalarPresheaf_primeCast (Y : Scheme.{u})
    (iY : Y ⟶ Spec (CommRingCat.of R)) (p : ℕ) (hR : (p : R) = 0)
    (O : Y.Opensᵒᵖ) : (p : Y.presheaf.obj O) = 0 := by
  let φ := (Y.presheaf.map (homOfLE (show O.unop ≤ ⊤ from le_top)).op).hom.comp
    (schemeScalarHom Y iY)
  simpa only [map_natCast, map_zero] using congrArg φ hR

variable {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))

/-- 同じ実際の nerve の全ての切断環の標数を、元の基底環から供給する。 -/
theorem schemeCechNervePresheaf_primeCast (p : ℕ) (hR : (p : R) = 0)
    (n : SimplexCategoryᵒᵖ) (O : ((Arrow.mk f).cechNerve.obj n).Opensᵒᵖ) :
    (p : ((Arrow.mk f).cechNerve.obj n).presheaf.obj O) = 0 :=
  schemeScalarPresheaf_primeCast _ ((Arrow.mk f).augmentedCechNerve.hom.app n) p hR O

/-- 実際の nerve の全ての射は、同じ増大項からの大域スカラーを保つ。 -/
theorem schemeCechNerveScalarHom_naturality {m n : SimplexCategoryᵒᵖ} (a : m ⟶ n) :
    schemeScalarHom ((Arrow.mk f).cechNerve.obj m)
        ((Arrow.mk f).augmentedCechNerve.hom.app m) =
      ((Arrow.mk f).cechNerve.map a).appTop.hom.comp
        (schemeScalarHom ((Arrow.mk f).cechNerve.obj n)
          ((Arrow.mk f).augmentedCechNerve.hom.app n)) := by
  apply schemeScalarHom_over
  simpa using (Arrow.mk f).augmentedCechNerve.hom.naturality a

end SerrePositivity.AlgebraicGeometry
