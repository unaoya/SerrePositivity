module

public import SerrePositivity.EInfinity.PowerOperation.MayCoefficientPrimitive
public import SerrePositivity.EInfinity.PowerOperation.MayClosedHomology

/-!
# May のノルム係数の零ホモロジー類

May, Proposition 2.3(ii) の同じ指定境界係数。
前の係数のノルムを、元の E(p) の実境界として閉元に束ねる。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.BarrattEccles

/-- 元の複体の実境界は、実際の kernel の閉元である。 -/
def mayClosedBoundary {k : Type u} [CommRing k] (K : Complex k) (i j : ℤ) (b : K.X i) :
    MayClosed K j :=
  ⟨K.d i j b, by
    have h := congrArg (fun f => f.hom b) (K.d_comp_d i j (j + 1))
    exact h⟩

lemma mayClosedBoundary_class {k : Type u} [CommRing k] (K : Complex k)
    (i j : ℤ) (h : i + 1 = j) (b : K.X i) :
    mayClosedClass K j (mayClosedBoundary K i j b) = 0 := by
  have hi : i = j - 1 := by omega
  subst i
  exact (mayClosedClass_eq_zero_iff K j _).mpr ⟨b, rfl⟩

variable (p : ℕ) [Fact p.Prime]

/-- 同じノルム係数を、指定した次の係数の実境界として保持する。 -/
def mayNormCoefficientClosed (s : ℕ) : MayClosed ((operad (ZMod p)).arity p) (-(s : ℤ)) :=
  mayClosedBoundary ((operad (ZMod p)).arity p) (-((s + 1 : ℕ) : ℤ)) (-(s : ℤ))
    (mayActualCoefficient p (s + 1) (mayAdditivityCoefficient p s))

lemma mayNormCoefficientClosed_value (s : ℕ) :
    (mayNormCoefficientClosed p s).val =
      mayActualCoefficient p s (((mayArityResolution p (ZMod p)).complex.X s).ρ.norm
        (mayCoefficientValue p (ZMod p) s)) := by
  exact mayAdditivityCoefficient_boundary p s

lemma mayNormCoefficientClosed_class (s : ℕ) :
    mayClosedClass ((operad (ZMod p)).arity p) (-(s : ℤ)) (mayNormCoefficientClosed p s) = 0 :=
  mayClosedBoundary_class _ _ _ (by push_cast; omega) _

end SerrePositivity.EInfinity.PowerOperation
