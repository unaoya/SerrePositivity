module

public import SerrePositivity.BhattScholze.Andre.PowerRootCoefficientQuotient
public import SerrePositivity.BhattScholze.Andre.PerfectPrismVarpi
public import SerrePositivity.BhattScholze.Andre.PowerRootCoefficientPDEnvelope

/-!
# André E1・E2：ϖ 還元した無限根入力環と原典の係数環

## 概要

完全 prism (A,(d)) で x=φ⁻¹(d)、ϖ=x mod d とする。
A/p 上の無限根環を x の係数像で割ると、R/ϖ 上の同じ無限根環と環同型。
BS Rem 7.15（著者版 p.62）の入力台環を具体的な商から得る。

## 方針

無限根環と係数主イデアル商の交換同型に、(A/p)/(x) と R/ϖ の係数同型を合成する。
係数・根変数・通常多項式の評価を計算する。

## 規約

prism 商の p 正則性もモニック性も、この入力環の同型自体には不要。

## 使われ方

還元後の実 pd 包を原典の R/ϖ 上のモニック入力と比較するための台環同型。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "G" => powerRootExponentMonoid p hp
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "barp" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "a" => barp (perfectPrismVarpiLift W hW)
local notation "N" => PowerRootPolynomial R₀ p hp
local notation "K" => Ideal.span {algebraMap R₀ N a}
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "barr" =>
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW}))
    (Ideal.Quotient.mk (OrientedPrism.ideal W))

/-- 概要：係数商同型の逆も A の代表元を保つ。
方針：順方向の代表元公式と逆合成を使う。
規約：逆の向きは (A/p)/(x) から R/ϖ。
使われ方：BS Rem 7.15（著者版 p.62）の単項式係数の照合。 -/
theorem perfectPrismVarpiQuotientEquiv_symm_mk (b : A) :
    (perfectPrismVarpiQuotientEquiv W hW).symm
      (Ideal.Quotient.mk _ (barp b)) = barr b := by
  apply (perfectPrismVarpiQuotientEquiv W hW).injective
  rw [RingEquiv.apply_symm_apply]
  exact (perfectPrismVarpiQuotientEquiv_mk W hW b).symm

/-- 概要：x mod p で係数還元した無限根環と R/ϖ 上の無限根環は環同型。
方針：係数商の交換と係数環同型のモノイド環への持上げを合成する。
規約：実際の係数主イデアル K による商を取る。
使われ方：BS Rem 7.15（著者版 p.62）の入力台環の具体化。 -/
def perfectPrismVarpiRootInputEquiv : (N ⧸ K) ≃+* Nv :=
  (powerRootCoefficientQuotientEquiv R₀ p hp a).trans
    (AddMonoidAlgebra.mapRingEquiv G (perfectPrismVarpiQuotientEquiv W hW).symm)

/-- 概要：入力環同型は A 由来の単項式の係数を同じ R/ϖ 係数へ送る。
方針：商比較と係数同型の単項式公式を合成する。
規約：指数は変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の入力元の同定。 -/
theorem perfectPrismVarpiRootInputEquiv_single (q : G) (b : A) :
    perfectPrismVarpiRootInputEquiv W hW
      (Ideal.Quotient.mk K (AddMonoidAlgebra.single q (barp b))) =
        AddMonoidAlgebra.single q (barr b) := by
  simp only [perfectPrismVarpiRootInputEquiv, RingEquiv.trans_apply,
    powerRootCoefficientQuotientEquiv_mk, powerRootCoefficientQuotientMap_single,
    AddMonoidAlgebra.mapRingEquiv_single, perfectPrismVarpiQuotientEquiv_symm_mk]

/-- 概要：入力環同型は元の係数環 A の像を保つ。
方針：係数を零指数の単項式として計算する。
規約：両側で標準係数射を用いる。
使われ方：BS Rem 7.15（著者版 p.62）の多項式係数の照合。 -/
theorem perfectPrismVarpiRootInputEquiv_coeff (b : A) :
    perfectPrismVarpiRootInputEquiv W hW
      (Ideal.Quotient.mk K (algebraMap R₀ N (barp b))) =
        algebraMap Rv Nv (barr b) := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using
    perfectPrismVarpiRootInputEquiv_single W hW 0 b

/-- 概要：入力環同型は全ての根変数を同じ番号の根変数へ送る。
方針：係数 1 の単項式の比較を使う。
規約：任意の段 n を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の通常変数での評価の比較。 -/
theorem perfectPrismVarpiRootInputEquiv_variable (n : ℕ) :
    perfectPrismVarpiRootInputEquiv W hW
      (Ideal.Quotient.mk K (powerRootPolynomialVariable R₀ p hp n)) =
        powerRootPolynomialVariable Rv p hp n := by
  simpa only [powerRootPolynomialVariable, map_one] using
    perfectPrismVarpiRootInputEquiv_single W hW (powerRootVariableExponent p hp n) 1

/-- 概要：名前付きモニック入力の係数還元は R/ϖ 上の同じ多項式の評価。
方針：評価の環射に関する自然性と係数・変数の照合を使う。
規約：等式にはモニック性を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の原典の f との同定。 -/
theorem perfectPrismVarpiRootInputEquiv_input (f : Polynomial A) :
    perfectPrismVarpiRootInputEquiv W hW
      (Ideal.Quotient.mk K (powerRootCoefficientPDInput p f)) =
        powerRootPolynomialBaseMap Rv p hp (f.map barr) := by
  unfold powerRootCoefficientPDInput powerRootPolynomialBaseMap
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  change (perfectPrismVarpiRootInputEquiv W hW).toRingHom
    (Polynomial.eval₂ ((Ideal.Quotient.mk K).comp ((algebraMap R₀ N).comp barp))
      (Ideal.Quotient.mk K (powerRootPolynomialVariable R₀ p hp 0)) f) = _
  rw [Polynomial.hom_eval₂]
  change Polynomial.eval₂ _
    (perfectPrismVarpiRootInputEquiv W hW
      (Ideal.Quotient.mk K (powerRootPolynomialVariable R₀ p hp 0))) f = _
  rw [perfectPrismVarpiRootInputEquiv_variable, Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1
  apply RingHom.ext
  intro b
  exact perfectPrismVarpiRootInputEquiv_coeff W hW b

/-- 概要：係数還元後のモニック入力は元の実商台環でも正則。
方針：原典の係数環上のモニック入力の正則性を比較同型で戻す。
規約：prism 商の p 正則性や f の正次数は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の還元後の pd 入力。 -/
theorem perfectPrismVarpiRootInput_monic_regular (f : Polynomial A) (hf : f.Monic) :
    IsSMulRegular (N ⧸ K) (Ideal.Quotient.mk K (powerRootCoefficientPDInput p f)) := by
  let e := perfectPrismVarpiRootInputEquiv W hW
  have hr := powerRootPolynomial_monic_regular Rv p hp (f.map barr) (hf.map barr)
  intro t s hts
  apply e.injective
  apply hr
  have h := congrArg e hts
  simpa only [e, smul_eq_mul, map_mul, perfectPrismVarpiRootInputEquiv_input] using h

end SerrePositivity.BhattScholze.Andre
