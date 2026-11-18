module

public import SerrePositivity.EInfinity.PowerOperation.MayZeroOperation
public import SerrePositivity.EInfinity.BarrattEccles.Theory.HomologyAlgebraFunctor
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.ZMod

/-!
# May の D₀ の零次ホモロジーへの降下

May, Proposition 2.3(iii) の零次部分。同じ係数の作用から定めた値の
代表元独立性と自然性を示す。F_p 上では加法的である。
正次数の係数を使う全次数の操作は別に構成する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.HomologyZero

variable {k : Type u} [CommRing k]
local instance mayHomologyCommRing (X : (operad k).Algebra) :
    CommRing (X.carrier.homology 0) := homologyCommRing X

variable (X : (operad k).Algebra) (p : ℕ) [NeZero p]

/-- May Proposition 2.3(iii)：同じ D₀ を選んだ代表へ適用した零次の値。 -/
def mayDZeroHomology (x : X.carrier.homology 0) : X.carrier.homology 0 :=
  mayDZeroRepresentative X p (_root_.SerrePositivity.HomologyZero.representative X.carrier x)

lemma mayDZeroHomology_value (x : X.carrier.homology 0) :
    mayDZeroHomology X p x = x ^ p := by
  rw [mayDZeroHomology, mayDZeroRepresentative_value, _root_.SerrePositivity.HomologyZero.representative_class]

/-- 選び直した代表射にも、同じ係数を使った値が一致する。 -/
lemma mayDZeroRepresentative_independent
    (f g : 𝟙_ (Complex k) ⟶ X.carrier)
    (h : _root_.SerrePositivity.HomologyZero.unitClass X.carrier f = _root_.SerrePositivity.HomologyZero.unitClass X.carrier g) :
    mayDZeroRepresentative X p f = mayDZeroRepresentative X p g := by
  rw [mayDZeroRepresentative_value, mayDZeroRepresentative_value, h]

lemma mayDZeroHomology_representative (f : 𝟙_ (Complex k) ⟶ X.carrier) :
    mayDZeroHomology X p (_root_.SerrePositivity.HomologyZero.unitClass X.carrier f) = mayDZeroRepresentative X p f := by
  rw [mayDZeroHomology_value, mayDZeroRepresentative_value]

/-- May Proposition 2.3(iii) の零次の値は全厳密 BE 射に自然。 -/
lemma mayDZeroHomology_naturality {Y : (operad k).Algebra} (f : X ⟶ Y)
    (x : X.carrier.homology 0) :
    homologyMap f.hom 0 (mayDZeroHomology X p x) =
      mayDZeroHomology Y p (homologyMap f.hom 0 x) := by
  rw [mayDZeroHomology_value, mayDZeroHomology_value]
  exact map_pow ((homologyAlgebraFunctor k).map f).hom x p

section PrimeField
variable (p : ℕ) [Fact p.Prime] (X : (operad (ZMod p)).Algebra)

/-- 零環も許す F_p 代数の H⁰ では、p 倍の単位は零。 -/
lemma mayHomology_prime_cast_zero : (p : X.carrier.homology 0) = 0 := by
  let := homologyAlgebra X
  have h := congrArg (algebraMap (ZMod p) (X.carrier.homology 0))
    (CharP.cast_eq_zero (ZMod p) p)
  simpa only [map_natCast, map_zero] using h

/-- May Proposition 2.3(iii) の零次の加法性。零環での CharP を仮定しない。 -/
lemma mayDZeroHomology_add (x y : X.carrier.homology 0) :
    mayDZeroHomology X p (x + y) = mayDZeroHomology X p x + mayDZeroHomology X p y := by
  simp only [mayDZeroHomology_value]
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : p.Prime) x y
  simpa only [mayHomology_prime_cast_zero p X, zero_mul, add_zero] using hr

/-- 零次の May の操作を可換群の準同型として束ねる。 -/
def mayDZeroHomologyAddHom : X.carrier.homology 0 →+ X.carrier.homology 0 where
  toFun := mayDZeroHomology X p
  map_zero' := by
    rw [mayDZeroHomology_value, zero_pow (Fact.out : p.Prime).ne_zero]
  map_add' := mayDZeroHomology_add p X

end PrimeField
end SerrePositivity.EInfinity.PowerOperation
