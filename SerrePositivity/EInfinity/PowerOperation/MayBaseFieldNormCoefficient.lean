module

public import SerrePositivity.EInfinity.PowerOperation.MayBaseFieldPrimitive
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
def mayBaseFieldClosedBoundary {k : Type u} [CommRing k] (K : Complex k) (i j : ℤ) (b : K.X i) :
    MayClosed K j :=
  ⟨K.d i j b, by
    have h := congrArg (fun f => f.hom b) (K.d_comp_d i j (j + 1))
    exact h⟩

lemma mayBaseFieldClosedBoundary_class {k : Type u} [CommRing k] (K : Complex k)
    (i j : ℤ) (h : i + 1 = j) (b : K.X i) :
    mayClosedClass K j (mayBaseFieldClosedBoundary K i j b) = 0 := by
  have hi : i = j - 1 := by omega
  subst i
  exact (mayClosedClass_eq_zero_iff K j _).mpr ⟨b, rfl⟩

variable {k : Type u} [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- 同じノルム係数を、指定した次の係数の実境界として保持する。 -/
def mayBaseFieldNormCoefficientClosed (s : ℕ) : MayClosed ((operad k).arity p) (-(s : ℤ)) :=
  mayBaseFieldClosedBoundary ((operad k).arity p) (-((s + 1 : ℕ) : ℤ)) (-(s : ℤ))
    (mayActualCoefficient p (s + 1) (mayBaseFieldAdditivityCoefficient p s))

lemma mayBaseFieldNormCoefficientClosed_value (s : ℕ) :
    (mayBaseFieldNormCoefficientClosed p s).val =
      mayActualCoefficient p s (((mayArityResolution p k).complex.X s).ρ.norm
        (mayCoefficientValue p k s)) := by
  exact mayBaseFieldAdditivityCoefficient_boundary p s

omit [CharP k p] in
lemma mayBaseFieldNormCoefficientClosed_class (s : ℕ) :
    mayClosedClass ((operad k).arity p) (-(s : ℤ)) (mayBaseFieldNormCoefficientClosed p s) = 0 :=
  mayBaseFieldClosedBoundary_class _ _ _ (by push_cast; omega) _

end SerrePositivity.EInfinity.PowerOperation
