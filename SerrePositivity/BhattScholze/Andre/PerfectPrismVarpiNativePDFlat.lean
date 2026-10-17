module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismVarpiNativePDEnvelope

/-!
# André E1・E2：原典の係数環上の実 pd 包の切断表示と忠実平坦性

## 概要

R/ϖ 上の無限根環のモニック入力の同じ pd 表示環は、入力の p 乗商上の可算切断表示を
持ち、係数環上自由、入力が正次数なら忠実平坦となる。
BS Rem 7.15(1)（著者版 p.62）の通常代数計算を原典の係数環に接続する。

## 方針

R/ϖ が p を殺すことを具体的な係数商同型から示す。
検証済みの切断表示同型と無限根モニック冪商の基底・忠実平坦性を同じ台環へ適用する。

## 規約

今回の環同型・加群の結果は prism 商の p 正則性を要求しない。
分冪値の公式は別ファイルの無条件版で提供する。

## 使われ方

原典の pd 包の通常平坦性計算を prismatic envelope との後続比較に供給する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zv" f => powerRootPolynomialBaseMap Rv p hp (Polynomial.map barr f)
local notation "Dv" f => PrincipalDPPresentation Nv (zv f)

/-- 概要：原典の R/ϖ 係数環で p は零。
方針：(A/p)/(x) との環同型で p の消滅を移す。
規約：p ねじれなしの仮定は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の標数 p の切断表示への入力。 -/
theorem perfectPrismVarpiCoefficient_prime_eq_zero : (p : Rv) = 0 := by
  apply (perfectPrismVarpiQuotientEquiv W hW).injective
  rw [map_natCast, map_zero]
  change Ideal.Quotient.mk _ (p : R₀) = 0
  have hp₀ : (p : R₀) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (p : A))
  rw [hp₀, map_zero]

/-- 概要：原典係数上の無限根環でも p は零。
方針：係数環の等式を標準係数射で送る。
規約：無限根環の台環は既存の単項式環。
使われ方：BS Rem 7.15(1)（著者版 p.62）の同じ表示環の切断表示。 -/
theorem perfectPrismVarpiRootRing_prime_eq_zero : (p : Nv) = 0 := by
  simpa only [map_natCast, map_zero] using
    congrArg (algebraMap Rv Nv) (perfectPrismVarpiCoefficient_prime_eq_zero W hW)

/-- 概要：原典係数上のモニック入力の pd 表示環は可算切断表示と代数同型。
方針：標数 p の標準表示同型を同じ入力台環へ適用する。
規約：入力の p 乗商の作用は既存の principalDPQuotientAlgebra を固定する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の P/(f^p)[gᵢ]/(gᵢ^p) の表示。 -/
def perfectPrismVarpiNativePDEnvelope_truncatedEquiv (f : Polynomial A) :
    letI := principalDPQuotientAlgebra hp (perfectPrismVarpiRootRing_prime_eq_zero W hW) (zv f)
    (Dv f) ≃ₐ[Nv ⧸ Ideal.span {(zv f) ^ p}] PrincipalDPTruncatedPresentation p (zv f) :=
  principalDPTruncatedQuotientAlgEquiv p (perfectPrismVarpiRootRing_prime_eq_zero W hW) _

/-- 概要：原典係数上の pd 包は入力の p 乗商上自由。
方針：切断表示の基底を係数商上の同型で戻す。
規約：モニック性も正次数もこの係数商上の自由性には不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の明示切断表示の自由性。 -/
theorem perfectPrismVarpiNativePDEnvelope_free_over_powerQuotient (f : Polynomial A) :
    letI := principalDPQuotientAlgebra hp (perfectPrismVarpiRootRing_prime_eq_zero W hW) (zv f)
    Module.Free (Nv ⧸ Ideal.span {(zv f) ^ p}) (Dv f) :=
  principalDPPresentation_free_via_truncated p (perfectPrismVarpiRootRing_prime_eq_zero W hW) _

/-- 概要：原典係数上の同じモニック pd 包の台環は R/ϖ 上自由。
方針：通常モニック冪商と切断表示の自由性をスカラー塔で合成する既存の定理を使う。
規約：零係数環と定数モニック入力を含む。
使われ方：BS Rem 7.15（著者版 p.62）の通常平坦性計算。 -/
theorem perfectPrismVarpiNativePDEnvelope_free (f : Polynomial A) (hf : f.Monic) :
    Module.Free Rv (Dv f) :=
  powerRootMonicDPPresentation_free Rv p hp (Fact.out : p.Prime)
    (perfectPrismVarpiCoefficient_prime_eq_zero W hW) (f.map barr) (hf.map barr)

/-- 概要：原典係数上の正次数モニック pd 包の台環は R/ϖ 上忠実平坦。
方針：非零係数環ではモニック次数保存、零係数環では加群の自明性を使う。
規約：正次数は元の多項式 f に要求する。
使われ方：BS Rem 7.15（著者版 p.62）の原典係数での忠実平坦性。 -/
theorem perfectPrismVarpiNativePDEnvelope_faithfullyFlat
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat Rv (Dv f) := by
  rcases subsingleton_or_nontrivial Rv with hs | hn
  · let := hs
    let := perfectPrismVarpiNativePDEnvelope_free W hW f hf
    rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
    refine ⟨inferInstance, ?_⟩
    intro T _ _ _
    exact Module.subsingleton Rv T
  · let := hn
    apply powerRootMonicDPPresentation_faithfullyFlat Rv p hp (Fact.out : p.Prime)
      (perfectPrismVarpiCoefficient_prime_eq_zero W hW) (f.map barr) (hf.map barr)
    simpa only [hf.natDegree_map barr] using hdeg

/-- 概要：原典の無限根入力環自体も R/ϖ 上自由。
方針：同じ指数モノイドの単項式基底を使う。
規約：係数環の非零性や入力多項式は不要。
使われ方：BS Rem 7.15（著者版 p.62）の通常代数計算の最初の自由性。 -/
theorem perfectPrismVarpiRootInput_free : Module.Free Rv Nv :=
  powerRootPolynomial_free Rv p hp

/-- 概要：原典のモニック入力の p 乗による実商は R/ϖ 上自由。
方針：モニック冪商の既存の基底を評価された入力の主イデアル商へ移す。
規約：正次数や prism 商の p 正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の P/(f^p) の自由性。 -/
theorem perfectPrismVarpiRootPowerQuotient_free (f : Polynomial A) (hf : f.Monic) :
    Module.Free Rv (Nv ⧸ Ideal.span {(zv f) ^ p}) := by
  let := powerRootPolynomialBaseAlgebra Rv p hp
  have h := powerRootPolynomialPowerQuotient_free Rv p hp (f.map barr) (hf.map barr)
  change Module.Free Rv
    (Nv ⧸ (Ideal.span {(f.map barr) ^ p}).map (algebraMap (Polynomial Rv) Nv)) at h
  rw [powerRootPolynomialQuotient_ideal, map_pow] at h
  exact h


end SerrePositivity.BhattScholze.Andre
