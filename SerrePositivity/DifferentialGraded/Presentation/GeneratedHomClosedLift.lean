module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomCochainLift
/-!
概要：係数 span に入る元の閉次数零射をコードの実閉射へ持ち上げる。
方針：閉射の零 cycle を同じ次数で持ち上げ、単位複体からの射へ戻す。
規約：実評価後に元の同じ閉射へ厳密に一致させる。
使われ方：c′ の追加係数から実関手と閉射を同時に回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {I : Type u} (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (source target : I → Set.Iio a) (degree : I → ℤ)
  (value : Set.Iio a → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ)
namespace DGGeneratedHomWord
variable (x y : (code R D κ a source target degree value coefficient hκ hI).Objects R κ)
  (f : ForgetEnrichment.of (Complex R) (value x) ⟶ ForgetEnrichment.of (Complex R) (value y))
  (hf : (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val ∈
    linearSpan source target degree R D value coefficient x y 0)

def codeClosedLiftCycle : zeroCycles (homObject R
    ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) x y) :=
  ⟨codeCochainLift R D κ a source target degree value coefficient hκ hI x y 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val hf,
    codeCochainLift_differential R D κ a source target degree value coefficient hκ hI x y 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val hf
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).property⟩

def codeClosedLift : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y :=
  ForgetEnrichment.homOf (Complex R)
    (unitFromCycle _ (codeClosedLiftCycle R D κ a source target degree value coefficient hκ hI x y f hf))

lemma codeClosedLift_map :
    (codeEvaluation R D κ a source target degree value coefficient hκ hI).onClosed.map
      (codeClosedLift R D κ a source target degree value coefficient hκ hI x y f hf) = f := by
  change unitFromCycle _ (codeClosedLiftCycle R D κ a source target degree value coefficient hκ hI x y f hf) ≫
    (codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y =
      ForgetEnrichment.homTo (Complex R) f
  apply (unitCycleEquiv _).injective
  change cycleFromUnit _ (_ ≫ _) = cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)
  apply Subtype.ext
  rw [cycleFromUnit_postcomp, cycleFromUnit_unitFromCycle]
  exact codeCochainLift_map R D κ a source target degree value coefficient hκ hI x y 0 _ hf

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
