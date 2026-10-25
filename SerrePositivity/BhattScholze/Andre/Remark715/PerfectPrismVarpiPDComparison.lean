module

public import SerrePositivity.BhattScholze.Andre.Remark715.PrincipalDPCoefficientQuotient
public import SerrePositivity.BhattScholze.Andre.Remark715.PerfectPrismVarpiRootInput
public import SerrePositivity.BhattScholze.Andre.Remark715.PerfectPrismVarpiRegular

/-!
# André E1・E2：ϖ 還元した pd 表示環と原典の入力上の標準表示

## 概要

無限根環上の pd 表示環を x=φ⁻¹(d) の係数像で割った実商は、R/ϖ 上の無限根環の
同じ多項式入力の標準 pd 表示と環同型。BS Rem 7.15(1)（著者版 p.62）の台環比較。

## 方針

一次関係商と係数商の交換同型を、無限根入力環の比較で誘導される表示環同型と合成する。
係数と全標準分冪生成元の像を計算する。

## 規約

通常環同型自体には prism 商の p 正則性もモニック性も要求しない。
prismatic envelope の Frobenius 引戻しとの同定はまだ含まない。

## 使われ方

構成済みの実分冪構造と普遍性を、原典の R/ϖ 係数上の標準台環へ移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "barp" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "a" => barp (perfectPrismVarpiLift W hW)
local notation "N" => PowerRootPolynomial R₀ p hp
local notation "z" => powerRootCoefficientPDInput p f
local notation "D" => PowerRootCoefficientPDEnvelope p f
local notation "K" => Ideal.span {algebraMap R₀ D a}
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zv" => powerRootPolynomialBaseMap Rv p hp (f.map barr)
local notation "Dv" => PrincipalDPPresentation Nv zv

/-- 概要：ϖ の持上げで還元した pd 表示環は原典の係数環上の標準表示と環同型。
方針：係数主イデアル商の交換と入力環の同型による表示環の移送を合成する。
規約：実商 D/(x mod p) と標準表示そのものを対象にする。
使われ方：BS Rem 7.15(1)（著者版 p.62）の還元後の pd 包の同定。 -/
def perfectPrismVarpiPDEnvelopeEquiv : (D ⧸ K) ≃+* Dv :=
  principalDPReducedCoefficientEquiv (algebraMap R₀ N a) z (algebraMap R₀ D a)
    (IsScalarTower.algebraMap_apply R₀ N D a) (perfectPrismVarpiRootInputEquiv W hW)
    zv (perfectPrismVarpiRootInputEquiv_input W hW f)

/-- 概要：表示環比較は全標準分冪生成元の次数を保つ。
方針：二つの比較同型の生成元公式を合成する。
規約：次数零も含む。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実分冪構造の移送。 -/
theorem perfectPrismVarpiPDEnvelopeEquiv_generator (n : ℕ) :
    perfectPrismVarpiPDEnvelopeEquiv W hW f (Ideal.Quotient.mk K (principalDPGenerator z n)) =
      principalDPGenerator zv n := by
  have h := principalDPReducedCoefficientEquiv_generator
    (algebraMap R₀ N a) z (algebraMap R₀ D a) (IsScalarTower.algebraMap_apply R₀ N D a)
    (perfectPrismVarpiRootInputEquiv W hW) zv
    (perfectPrismVarpiRootInputEquiv_input W hW f) n
  unfold perfectPrismVarpiPDEnvelopeEquiv
  with_reducible exact h

/-- 概要：表示環比較は元の係数環 A の像を保つ。
方針：係数作用の塔を展開し、係数商比較と入力環比較の係数公式を使う。
規約：R/ϖ 上の標準係数射で値を述べる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数代数としての比較。 -/
theorem perfectPrismVarpiPDEnvelopeEquiv_coeff (b : A) :
    perfectPrismVarpiPDEnvelopeEquiv W hW f
      (Ideal.Quotient.mk K (algebraMap R₀ D (barp b))) =
        algebraMap Nv Dv (algebraMap Rv Nv (barr b)) := by
  have h := principalDPReducedCoefficientEquiv_coeff
    (algebraMap R₀ N a) z (algebraMap R₀ D a) (IsScalarTower.algebraMap_apply R₀ N D a)
    (perfectPrismVarpiRootInputEquiv W hW) zv
    (perfectPrismVarpiRootInputEquiv_input W hW f) (algebraMap R₀ N (barp b))
  rw [perfectPrismVarpiRootInputEquiv_coeff] at h
  have hc := congrArg (fun t : D => perfectPrismVarpiPDEnvelopeEquiv W hW f
    (Ideal.Quotient.mk K t)) (IsScalarTower.algebraMap_apply R₀ N D (barp b))
  exact hc.trans h

/-- 概要：表示環比較は pd 入力元を原典の係数環上の同じ入力元へ送る。
方針：次数一の標準分冪生成元と入力係数の関係を使う。
規約：等式にモニック性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の構造比較。 -/
theorem perfectPrismVarpiPDEnvelopeEquiv_input :
    perfectPrismVarpiPDEnvelopeEquiv W hW f
      (Ideal.Quotient.mk K (algebraMap N D z)) = algebraMap Nv Dv zv := by
  simpa only [principalDPGenerator_one] using
    perfectPrismVarpiPDEnvelopeEquiv_generator W hW f 1

/-- 概要：還元した正次数分冪イデアルは原典の入力の正次数イデアルに対応する。
方針：像の合成と生成集合の像を計算し、全標準生成元の対応を使う。
規約：イデアルの等式は実表示環同型の像として述べる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実分冪構造の移送の入力。 -/
theorem perfectPrismVarpiPDEnvelopeEquiv_positiveIdeal :
    ((principalDPPositiveIdeal z).map (Ideal.Quotient.mk K)).map
      (perfectPrismVarpiPDEnvelopeEquiv W hW f).toRingHom = principalDPPositiveIdeal zv := by
  rw [Ideal.map_map, principalDPPositiveIdeal, Ideal.map_span, ← Set.range_comp']
  change Ideal.span (Set.range fun n : ℕ => perfectPrismVarpiPDEnvelopeEquiv W hW f
    (Ideal.Quotient.mk K (principalDPGenerator z (n + 1)))) = _
  simp only [perfectPrismVarpiPDEnvelopeEquiv_generator, principalDPPositiveIdeal]

end SerrePositivity.BhattScholze.Andre
