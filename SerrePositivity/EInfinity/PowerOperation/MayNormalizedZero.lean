module

public import SerrePositivity.EInfinity.PowerOperation.MayZeroActionEvaluation
public import SerrePositivity.EInfinity.PowerOperation.MayZeroClassComparison
public import SerrePositivity.EInfinity.PowerOperation.MayNormalizedClasses

/-!
# 規格化した全次数 P⁰ の零次の値

May, Proposition 2.3(iii)。全次数の指定 D_i の零次成分を、
同じ単位射に対する既存の D₀ の p 乗計算と照合する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open SerrePositivity.EInfinity.BarrattEccles SerrePositivity.EInfinity.HomologyZero
variable {k : Type u} [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
variable (X : (operad k).Algebra)

lemma mayClosedIndex_val (K : Complex k) {i j : ℤ} (h : i = j) (a : MayClosed K i) :
    (mayClosedIndex K h a).val =
      (eqToHom (congrArg (fun t : ℤ => K.X t) h)).hom a.val := by
  subst j
  rfl

/-- 同じ D₀ の閉元は、単位射による同じ係数作用の閉元そのもの。 -/
lemma mayDZeroClosed_unit (f : 𝟙_ (Complex k) ⟶ X.carrier) :
    mayClosedIndex X.carrier
      ((zero_add (mayRepeatedDegree 0 p)).trans (mayRepeatedZeroDegree p))
        (mayDClosed X p 0 0 (cycleFromUnit X.carrier f)) =
      cycleFromUnit X.carrier
        (repeatedUnitInput f p ≫ coefficientOperation X p (mayZeroCoefficient p k)) := by
  apply Subtype.ext
  rw [mayClosedIndex_val]
  change (eqToHom (congrArg (fun i : ℤ => X.carrier.X i)
    ((zero_add (mayRepeatedDegree 0 p)).trans (mayRepeatedZeroDegree p)))).hom
      (mayDValue X p 0 0 (f.f 0 (mayTensorUnitValue (k := k)))) = _
  unfold mayDValue
  have ht := mayHomogeneousAction_zero_transport X p (mayRepeatedDegree 0 p)
    (mayRepeatedZeroDegree p) (mayActualCoefficient p 0 (mayCoefficientValue p k 0))
      (mayRepeatedValue X.carrier 0 (f.f 0 (mayTensorUnitValue (k := k))) p)
  refine ht.trans ?_
  change mayHomogeneousAction X p 0 0
    (mayActualCoefficient p 0 (mayCoefficientValue p k 0))
      (mayRepeatedZeroValue X.carrier (f.f 0 (mayTensorUnitValue (k := k))) p) = _
  rw [← mayRepeatedUnitInput_value f p, ← mayZeroCoefficientOperation_value]
  rfl

/-- 添字の等式を先に指定し、依存する次数の移送を同じ証明で読む。 -/
lemma mayNormalizedClass_index_view (n : ℤ) (c : k) (hn : 0 ≤ mayZeroIndex p n)
    (i : ℕ) (hi : (mayZeroIndex p n).toNat = i)
    (hd : -(i : ℤ) + mayRepeatedDegree (-n) p = -n) (a : MayClosed X.carrier (-n)) :
    mayNormalizedClass p X n c a =
      c • (eqToHom (congrArg (fun t : ℤ => X.carrier.homology t) hd)).hom
        (mayDClass p X i (-n) a) := by
  subst i
  unfold mayNormalizedClass
  exact dite_eq_left hn

local instance mayNormalizedZeroCommRing : CommRing (X.carrier.homology 0) := homologyCommRing X

/-- ν(0)=1 の場合の、全次数の構成と既存 D₀ の計算の一致。 -/
lemma mayNormalizedClass_zero_unit (f : 𝟙_ (Complex k) ⟶ X.carrier) :
    mayNormalizedClass p X 0 1 (cycleFromUnit X.carrier f) = unitClass X.carrier f ^ p := by
  have hn : 0 ≤ mayZeroIndex p 0 := by rw [mayZeroIndex_zero]
  have hi : (mayZeroIndex p 0).toNat = 0 := by rw [mayZeroIndex_zero]; rfl
  have hd : -(0 : ℤ) + mayRepeatedDegree 0 p = 0 :=
    (zero_add (mayRepeatedDegree 0 p)).trans (mayRepeatedZeroDegree p)
  have hview := mayNormalizedClass_index_view p X 0 1 hn 0 hi hd (cycleFromUnit X.carrier f)
  rw [one_smul] at hview
  refine hview.trans ?_
  have hclass := mayClosedClass_index X.carrier hd (mayDClosed X p 0 0 (cycleFromUnit X.carrier f))
  refine hclass.symm.trans ?_
  refine (congrArg (mayClosedClass X.carrier 0) (mayDZeroClosed_unit p X f)).trans ?_
  exact (mayClosedClass_cycleFromUnit X.carrier
    (repeatedUnitInput f p ≫ coefficientOperation X p (mayZeroCoefficient p k))).trans
      (mayDZeroRepresentative_value X p f)

/-- 全次数の同じ規格化された P⁰ は、実 H⁰ の環で p 乗。 -/
lemma mayNormalizedHomology_zero_value (x : X.carrier.homology 0) :
    mayNormalizedHomology p X 0 1 x = x ^ p := by
  obtain ⟨f, rfl⟩ := unitClass_surjective X.carrier x
  have hh := mayNormalizedHomology_class p X 0 1 (cycleFromUnit X.carrier f)
  exact hh.trans (mayNormalizedClass_zero_unit p X f)

end SerrePositivity.EInfinity.PowerOperation
