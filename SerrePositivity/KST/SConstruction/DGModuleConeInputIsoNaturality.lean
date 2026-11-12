module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalCone

/-!
概要：同じ実 cone の入力射等号による指定同型が元全 Hom 作用を保つことを示す。
方針：同じ二入力等号を消去し、元豊穣単位則へ戻す。
規約：第三成分零の元 cone 作用と指定入力等号を保持する。
使われ方：元厳密 gluing cone と全自然な module cone の全入力比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：元二入力等号の cone 同型は同じ零第三成分の全 Hom 作用と可換。
方針：元二入力の等号を消去し、同じ元斉次単位則を使う。
規約：同じ入力同型・全整数次数を保持。使われ方：実 cone 族の入力全比較。 -/
lemma dgModuleConeInputIso_naturality {M N M' N' : ModuleCategory R D}
    (f f' : M ⟶ N) (g g' : M' ⟶ N') (ef : f = f') (eg : g = g')
    (n : ℤ)
    (a : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) M')).X n)
    (b : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) N')).X n) :
    compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R D f))
      (y := ForgetEnrichment.to (Complex R) (moduleCone R D g))
      (z := ForgetEnrichment.to (Complex R) (moduleCone R D g'))
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (eqToIso (congrArg (fun t => moduleCone R D t) eg)).hom)).val
      (dgGluingModuleConeElement R D f g a b 0 (sub_add_cancel n 1)) (add_zero n) =
    compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R D f))
      (y := ForgetEnrichment.to (Complex R) (moduleCone R D f'))
      (z := ForgetEnrichment.to (Complex R) (moduleCone R D g'))
      (dgGluingModuleConeElement R D f' g' a b 0 (sub_add_cancel n 1))
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (eqToIso (congrArg (fun t => moduleCone R D t) ef)).hom)).val (zero_add n) := by
  cases ef
  cases eg
  simp only [eqToIso_refl, Iso.refl_hom]
  change compose R (unitElement R _).val _ (add_zero n) =
    compose R _ (unitElement R _).val (zero_add n)
  exact (unit_compose R _).trans (compose_unit R _).symm
end SerrePositivity.KST.SConstruction
