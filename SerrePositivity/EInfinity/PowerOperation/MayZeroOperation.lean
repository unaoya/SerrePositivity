module

public import SerrePositivity.EInfinity.PowerOperation.MayZeroCoefficient
public import SerrePositivity.EInfinity.PowerOperation.MayRepeatedInput
public import SerrePositivity.EInfinity.BarrattEccles.HomologyCompositeHomotopy
public import SerrePositivity.EInfinity.BarrattEccles.HomologyRing

/-!
# May の同じ D₀ の H⁰ 上の値

May, Proposition 2.3(iii) の零次計算。
同じ W→E(p) の零次係数を p 個の同じ代表射へ入力し、H⁰ で p 乗になることを示す。
全整数次数の代表元独立性・加法性は、この零次の計算とは別に示す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.HomologyZero
variable {k : Type u} [CommRing k] (X : (operad k).Algebra)

local instance mayZeroHomologyCommRing : CommRing (X.carrier.homology 0) := homologyCommRing X

/-- 同じ代表射を全入力へ入れた、既存の n 入力作用の H⁰ 値。 -/
def homologyRepeatedValue (f : 𝟙_ (Complex k) ⟶ X.carrier) (n : ℕ) :
    X.carrier.homology 0 :=
  _root_.SerrePositivity.HomologyZero.unitClass X.carrier (repeatedUnitInput f n ≫ homologyOperation X n)

lemma homologyRepeatedValue_zero (f : 𝟙_ (Complex k) ⟶ X.carrier) :
    homologyRepeatedValue X f 0 = 1 := by
  change _root_.SerrePositivity.HomologyZero.unitClass X.carrier (𝟙 _ ≫ homologyOperation X 0) = homologyOne X
  rw [Category.id_comp]
  rfl

lemma homologyRepeatedValue_succ (f : 𝟙_ (Complex k) ⟶ X.carrier) (n : ℕ) :
    homologyRepeatedValue X f (n + 1) =
      _root_.SerrePositivity.HomologyZero.unitClass X.carrier f * homologyRepeatedValue X f n := by
  have hb : (aritySection k n ▷ power X.carrier n) ≫ X.action n =
      (λ_ (power X.carrier n)).hom ≫ homologyOperation X n := by
    simp only [homologyOperation, Iso.hom_inv_id_assoc]
  have h := (homologyCompositionHomotopy X 1 n 1).compLeft (repeatedUnitInput f (1 + n))
  rw [hb] at h
  have h' : Homotopy
      (repeatedUnitInput f (1 + n) ≫ homologyOperation X (1 + n))
      (_root_.SerrePositivity.HomologyZero.unitPairing (homologyBinary X) f
        (repeatedUnitInput f n ≫ homologyOperation X n)) := by
    change Homotopy _ ((λ_ (𝟙_ (Complex k))).inv ≫
      (f ⊗ₘ (repeatedUnitInput f n ≫ homologyOperation X n)) ≫
        (X.carrier ◁ (oneIso X.carrier).inv) ≫ homologyOperation X 2)
    simpa only [Category.assoc, reassoc_of% (repeatedUnitInput_secondInsertion f n
      (homologyOperation X n))] using h
  change _root_.SerrePositivity.HomologyZero.unitClass X.carrier (_ ≫ homologyOperation X (n + 1)) =
    _root_.SerrePositivity.HomologyZero.pairingValue (homologyBinary X) (_root_.SerrePositivity.HomologyZero.unitClass X.carrier f)
      (_root_.SerrePositivity.HomologyZero.unitClass X.carrier (repeatedUnitInput f n ≫ homologyOperation X n))
  rw [_root_.SerrePositivity.HomologyZero.pairingValue_class]
  apply (_root_.SerrePositivity.HomologyZero.unitClass_eq_iff X.carrier _ _).mpr
  have hn := congrArg (fun m => repeatedUnitInput f m ≫ homologyOperation X m) (Nat.one_add n)
  exact ⟨(Homotopy.ofEq hn.symm).trans h'⟩

lemma homologyRepeatedValue_pow (f : 𝟙_ (Complex k) ⟶ X.carrier) (n : ℕ) :
    homologyRepeatedValue X f n = _root_.SerrePositivity.HomologyZero.unitClass X.carrier f ^ n := by
  induction n with
  | zero => rw [homologyRepeatedValue_zero, pow_zero]
  | succ n ih => rw [homologyRepeatedValue_succ, ih, pow_succ']

variable (p : ℕ) [NeZero p]

/-- 同じ W→BE 比較の D₀ を、零次の同じ代表射に評価する。 -/
def mayDZeroRepresentative (f : 𝟙_ (Complex k) ⟶ X.carrier) : X.carrier.homology 0 :=
  _root_.SerrePositivity.HomologyZero.unitClass X.carrier (repeatedUnitInput f p ≫
    coefficientOperation X p (mayZeroCoefficient p k))

/-- May の同じ D₀ は、元の H⁰ の環で p 乗そのもの。 -/
lemma mayDZeroRepresentative_value (f : 𝟙_ (Complex k) ⟶ X.carrier) :
    mayDZeroRepresentative X p f = _root_.SerrePositivity.HomologyZero.unitClass X.carrier f ^ p := by
  have h := (coefficientOperationHomotopy X p (mayZeroCoefficientHomotopy p k)).compLeft
    (repeatedUnitInput f p)
  have hv : mayDZeroRepresentative X p f = homologyRepeatedValue X f p := by
    apply (_root_.SerrePositivity.HomologyZero.unitClass_eq_iff X.carrier _ _).mpr
    exact ⟨h⟩
  exact hv.trans (homologyRepeatedValue_pow X f p)

end SerrePositivity.EInfinity.PowerOperation
