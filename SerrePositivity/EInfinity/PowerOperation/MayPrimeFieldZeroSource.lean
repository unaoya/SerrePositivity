module

public import SerrePositivity.EInfinity.PowerOperation.MayNormalizedZero
public import SerrePositivity.EInfinity.PowerOperation.MayPiZeroSourceComparison
public import SerrePositivity.EInfinity.PowerOperation.MayZeroIsoTransport
public import SerrePositivity.EInfinity.PowerOperation.MayPrimeFieldLocalization

/-!
# 素体上の May の P⁰ の零次の計算を局所化へ運ぶ

May, Proposition 2.3(iii)・BS 著者版 Lemma 8.4(b)。
同じホモロジー比較・零次環の比較・指定演算を源で照合し、通常の局所化で全対象へ運ぶ。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.EInfinity.BarrattEccles
variable (p : ℕ) [Fact p.Prime]

abbrev mayPrimeFieldPiZeroComparison :=
  Functor.isoWhiskerRight (barrattEcclesPi0_forget (MayPrimeField.{u} p))
    (forget₂ (ModuleCat (MayPrimeField.{u} p)) AddCommGrpCat)

lemma mayPrimeFieldPowerZero_source_zero_map (X : (operad (MayPrimeField.{u} p)).Algebra) :
    (mayPrimeFieldPowerZero p 0).app ((ordinaryAlgebraHoSource (MayPrimeField.{u} p)).obj X) ≫
      (mayNormalizedHomologySourceIso (MayPrimeField.{u} p) 0).hom.app X =
    (mayNormalizedHomologySourceIso (MayPrimeField.{u} p) 0).hom.app X ≫
      (mayNormalizedStrictPowerZero p 0 (1 : MayPrimeField.{u} p)).app X := by
  let e := (mayNormalizedHomologySourceIso (MayPrimeField.{u} p) 0).app X
  have hx := congrArg (fun η => η.app X) (mayPrimeFieldPowerZero_source.{u} p 0)
  rw [mayNu_zero] at hx
  change (mayPrimeFieldPowerZero p 0).app _ = e.hom ≫
    (mayNormalizedStrictPowerZero p 0 (1 : MayPrimeField.{u} p)).app X ≫ e.inv at hx
  rw [hx]
  change (e.hom ≫ _ ≫ e.inv) ≫ e.hom = e.hom ≫ _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma mayPrimeFieldPiZeroComparison_source (X : (operad (MayPrimeField.{u} p)).Algebra)
    (a : ((barrattEcclesPi0 (MayPrimeField.{u} p)).obj
      ((ordinaryAlgebraHoSource (MayPrimeField.{u} p)).obj X)).right) :
    (mayNormalizedHomologySourceIso (MayPrimeField.{u} p) 0).hom.app X
      ((mayPrimeFieldPiZeroComparison p).hom.app
        ((ordinaryAlgebraHoSource (MayPrimeField.{u} p)).obj X) a) =
      (mayPiZeroSourceRight (MayPrimeField.{u} p)).hom.app X a :=
  mayPiZeroForget_source_apply (MayPrimeField.{u} p) X a

lemma mayPrimeFieldPowerZero_zero_source (X : (operad (MayPrimeField.{u} p)).Algebra) :
    MayZeroFrobeniusAt p (barrattEcclesPi0 (MayPrimeField.{u} p)) (mayPrimeFieldHomology p 0)
      (mayPrimeFieldPiZeroComparison p) (mayPrimeFieldPowerZero p 0)
        ((ordinaryAlgebraHoSource (MayPrimeField.{u} p)).obj X) := by
  intro a
  let _ : CommRing ((mayNormalizedStrictHomology (MayPrimeField.{u} p) 0).obj X) :=
    homologyCommRing X
  let _ : CommRing ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad (MayPrimeField.{u} p)) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat (MayPrimeField.{u} p)) (.up ℤ) 0).obj X) :=
      homologyCommRing X
  let e := (mayNormalizedHomologySourceIso (MayPrimeField.{u} p) 0).app X
  let z := (ordinaryAlgebraHoSource (MayPrimeField.{u} p)).obj X
  let c := mayPrimeFieldPiZeroComparison p
  apply e.addCommGroupIsoToAddEquiv.injective
  have ha := congrArg (fun f => f (c.hom.app z a)) (mayPrimeFieldPowerZero_source_zero_map p X)
  change e.hom ((mayPrimeFieldPowerZero p 0).app z (c.hom.app z a)) =
    mayNormalizedHomology p X 0 (1 : MayPrimeField.{u} p) (e.hom (c.hom.app z a)) at ha
  calc
    _ = mayNormalizedHomology p X 0 (1 : MayPrimeField.{u} p) (e.hom (c.hom.app z a)) := ha
    _ = (e.hom (c.hom.app z a) : X.carrier.homology 0) ^ p := mayNormalizedHomology_zero_value p X _
    _ = ((mayPiZeroSourceRight (MayPrimeField.{u} p)).hom.app X a : X.carrier.homology 0) ^ p := by
      exact congrArg
        (fun b : (mayNormalizedStrictHomology (MayPrimeField.{u} p) 0).obj X => b ^ p)
        (mayPrimeFieldPiZeroComparison_source p X a)
    _ = (mayPiZeroSourceRight (MayPrimeField.{u} p)).hom.app X (a ^ p) :=
      (mayPiZeroSourceRight_pow (MayPrimeField.{u} p) X a p).symm
    _ = _ := (mayPrimeFieldPiZeroComparison_source p X (a ^ p)).symm

/-- 任意の ho(CAlg F_p) 対象の零次環で、同じ P⁰ は p 乗。 -/
lemma mayPrimeFieldPowerZero_zero (z : (CAlg_R (MayPrimeField.{u} p)).HomotopyCategory) :
    MayZeroFrobeniusAt p (barrattEcclesPi0 (MayPrimeField.{u} p)) (mayPrimeFieldHomology p 0)
      (mayPrimeFieldPiZeroComparison p) (mayPrimeFieldPowerZero p 0) z := by
  let k := MayPrimeField.{u} p
  let L := ordinaryAlgebraHoSource k
  let W := ordinaryAlgebraWeak k
  let _ := ordinaryAlgebraHoSource_isLocalization k
  let _ := Localization.essSurj L W
  exact mayZeroFrobeniusAt_of_iso p (barrattEcclesPi0 k) (mayPrimeFieldHomology p 0)
    (mayPrimeFieldPiZeroComparison p) (mayPrimeFieldPowerZero p 0) (L.objObjPreimageIso z)
      (mayPrimeFieldPowerZero_zero_source p (L.objPreimage z))

end SerrePositivity.EInfinity.PowerOperation
