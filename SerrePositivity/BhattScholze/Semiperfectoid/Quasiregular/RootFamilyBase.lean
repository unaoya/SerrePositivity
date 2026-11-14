module

public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootFamilies.PowerRootPolynomial
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionComparisons
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion

/-!
# 根付き変数族の実 p 完備化

## 概要
任意の添字の根付きモノイド環と、その実主元完備化 H⁰ を定義する。
## 方針
ねじれを係数で評価し、既存の有界ねじれの完備化比較を適用する。
## 規約
BS 著者版 Proposition 7.10 の T・S′ の基底。drafts の rootBase と同じ実 H⁰ を用いる。
## 使われ方
根付き基底の perfectoid 性と有限個の Xi−fi の包絡。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.DerivedCompletion _root_.SerrePositivity.BhattScholze.Andre _root_.SerrePositivity.BhattScholze.Andre.Transfinite
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (J : Type v)

/-- 任意の変数族に非負 p 冪分数の指数を許すモノイド環。 -/
abbrev rootFamilyRaw :=
  AddMonoidAlgebra R (J →₀ _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentMonoid p (Fact.out : p.Prime).pos)

/-- 根付き変数環の実 p 完備化の H⁰。 -/
abbrev rootFamilyBase := PrincipalCompletionH0 (rootFamilyRaw p R J) (p : rootFamilyRaw p R J)

/-- 根付き基底には、既存の実主元完備化の H⁰ の環構造を使う。 -/
instance rootFamilyBaseCommRing : CommRing (rootFamilyBase p R J) :=
  principalCompletionCommRing _ _

/-- 生のモノイド環から実完備化への標準環射。 -/
def rootFamilyUnit : rootFamilyRaw p R J →+* rootFamilyBase p R J :=
  principalCompletionUnitRingHom _ _

/-- 生の係数射と実完備化の単位を合成し、根付き基底の係数作用を定める。 -/
instance rootFamilyBaseAlgebra : Algebra R (rootFamilyBase p R J) :=
  ((rootFamilyUnit p R J).comp (algebraMap R (rootFamilyRaw p R J))).toAlgebra

/-- j 番目の変数の n 段目の根。 -/
def rootFamilyVariable (j : J) (n : ℕ) : rootFamilyBase p R J :=
  rootFamilyUnit p R J (AddMonoidAlgebra.single
    (Finsupp.single j (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootVariableExponent p (Fact.out : p.Prime).pos n)) 1)

/-- 概要：生の根付き変数族の p 冪ねじれは、係数環と同じ指数で消える。
方針：各単項式の係数に入力の評価を適用する。
規約：BS 著者版 Proposition 7.10 の完備化前。係数環の非零性は不要。
使われ方：実 H⁰ と古典的完備化を比較する有界性。 -/
theorem rootFamilyRaw_torsion_bound (N : ℕ)
    (hR : ∀ n : ℕ, ∀ x : R, (p : R)^n * x = 0 → (p : R)^N * x = 0)
    (n : ℕ) (x : rootFamilyRaw p R J) (hx : (p : rootFamilyRaw p R J)^n * x = 0) :
    (p : rootFamilyRaw p R J)^N * x = 0 := by
  have h : (p : R)^n • x = 0 := by
    simpa only [Algebra.smul_def, map_pow, map_natCast] using hx
  have hz : (p : R)^N • x = 0 := by
    ext e
    have he := congrArg (fun y : rootFamilyRaw p R J => y.coeff e) h
    have he' : (p : R)^n * x.coeff e = 0 := by
      simpa only [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using he
    simpa only [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hR n (x.coeff e) he'
  simpa only [Algebra.smul_def, map_pow, map_natCast] using hz

/-- perfectoid 係数の場合、生の根付き変数環の p 冪ねじれは p で消える。 -/
theorem rootFamilyRaw_bounded (hR : IsIntegralPerfectoid R p) :
    ∃ N : ℕ, ∀ n : ℕ, ∀ x : rootFamilyRaw p R J,
      (p : rootFamilyRaw p R J)^n * x = 0 → (p : rootFamilyRaw p R J)^N * x = 0 :=
  ⟨1, rootFamilyRaw_torsion_bound p R J 1 (fun n x hx => by
    simpa only [pow_one] using hR.p_mul_eq_zero_of_pow_mul_eq_zero R p n x hx)⟩

/-- 概要：根付き変数環の実 H⁰ 完備化と古典的 p 完備化の環同型。
方針：生の環のねじれの評価を既存の有界主元完備化比較へ渡す。
規約：BS 著者版 Proposition 7.10。零環の枝を含む。
使われ方：原典の古典的な根付き基底との照合。 -/
def rootFamilyBaseAdicEquiv (hR : IsIntegralPerfectoid R p) :
    rootFamilyBase p R J ≃+*
      AdicCompletion (Ideal.span {(p : rootFamilyRaw p R J)}) (rootFamilyRaw p R J) :=
  by
    letI := principalCompletionAlgebra (rootFamilyRaw p R J) (p : rootFamilyRaw p R J)
    exact (boundedPrincipalCompletionAdicAlgEquiv _ _ (rootFamilyRaw_bounded p R J hR)).toRingEquiv

/-- 完備化比較は、生のモノイド環の単位と両立する。 -/
theorem rootFamilyBaseAdicEquiv_unit (hR : IsIntegralPerfectoid R p) (x : rootFamilyRaw p R J) :
    rootFamilyBaseAdicEquiv p R J hR (rootFamilyUnit p R J x) =
      algebraMap (rootFamilyRaw p R J) _ x :=
  by
    letI := principalCompletionAlgebra (rootFamilyRaw p R J) (p : rootFamilyRaw p R J)
    exact (boundedPrincipalCompletionAdicAlgEquiv _ _ (rootFamilyRaw_bounded p R J hR)).commutes x

end SerrePositivity.BhattScholze.Semiperfectoid
