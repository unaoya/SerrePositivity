module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Pair.RegularSwap
public import SerrePositivity.BhattScholze.Prism.Basic.GeneratorRegularity
public import SerrePositivity.BhattScholze.Andre.OrdinaryRoots.Adjoin

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Varpi
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PowerRootInput
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PowerRootPolynomial
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PrincipalDP

/-!
# ϖ 還元した pd 表示（BS 著者版 Remark 7.15 の φ*(T/ϖ) の計算）

## 概要
ϖ の持ち上げの mod p 正則性、ϖ 還元した無限根入力環と原典の係数環、ϖ 還元した pd 表示環と原典の標準表示、R/ϖ[Y^{1/p^∞}] 上の pd 包の比較・切断表示・忠実平坦性。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/CompletionPD`、`PowerRootEnvelope/DeltaDivisionResidue`、`PowerRootEnvelope/Initiality`、`PowerRootEnvelope/PrincipalPair`、`PowerRootEnvelope/Unconditional/Residue`、`PowerRootEnvelope/VarpiComparison`、`Variants/MonicRootedExtension`。
-/

universe u

/-! ## ϖ の持上げの mod p 正則性

## 概要

完全 prism (A,(d)) の商 R が p 正則なら、x=φ⁻¹(d) の mod p 像は正則。
BS 著者版 Remark 7.15（著者版 p.62）の p ねじれなしの場合の係数還元を具体化する。

## 方針

d の正則性と R の p 正則性から正則列の二元の順序を交換する。
mod p で x^p=d なので、正の冪から x 自身の正則性が従う。

## 規約

R の p 正則性を明示仮定とする。一般の perfectoid 基底へこの仮定を追加しない。

## 使われ方

原典の p ねじれなしの場合の中間計算を保持する。
実分冪降下の旧3宣言は不要になったため削除し、
Unconditional.VarpiPDReduction の射影的係数商による無条件版を使う。
置換先は原典と異なる線形切断による証明経路。
-/

@[expose] public noncomputable section PerfectPrismVarpiRegular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A]

variable {p : ℕ} [Fact p.Prime]

/-- 概要：選んだ ϖ の持上げは mod p で正則。
方針：mod p の x^p=d と正の冪の正則性判定を使う。
規約：p 正則性は prism 商に要求する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数還元における分冪安定性。 -/
theorem perfectPrismVarpiLift_modPrime_regular (W : OrientedPrism p A)
    (hW : W.deltaStructure.IsPerfect)
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)) :
    IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)) := by
  apply (IsSMulRegular.pow_iff (Nat.Prime.pos (Fact.out : p.Prime))).mp
  have h := congrArg (Ideal.Quotient.mk (Ideal.span {(p : A)}))
    (perfectPrismVarpiLift_frobenius W hW)
  rw [W.deltaStructure.frobeniusLift_apply, map_add, map_pow, map_mul] at h
  simp only [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (p : A)),
    zero_mul, add_zero] at h
  rw [h]
  exact perfectPrism_generator_modPrime_regular W hpR

end SerrePositivity.BhattScholze.Andre

end PerfectPrismVarpiRegular

/-! ## ϖ 還元した無限根入力環と原典の係数環

## 概要

完全 prism (A,(d)) で x=φ⁻¹(d)、ϖ=x mod d とする。
A/p 上の無限根環を x の係数像で割ると、R/ϖ 上の同じ無限根環と環同型。
BS 著者版 Remark 7.15（著者版 p.62）の入力台環を具体的な商から得る。

## 方針

無限根環と係数主イデアル商の交換同型に、(A/p)/(x) と R/ϖ の係数同型を合成する。
係数・根変数・通常多項式の評価を計算する。

## 規約

prism 商の p 正則性もモニック性も、この入力環の同型自体には不要。

## 使われ方

還元後の実 pd 包を原典の R/ϖ 上のモニック入力と比較するための台環同型。
-/

@[expose] public noncomputable section PerfectPrismVarpiRootInput

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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の単項式係数の照合。 -/
theorem perfectPrismVarpiQuotientEquiv_symm_mk (b : A) :
    (perfectPrismVarpiQuotientEquiv W hW).symm
      (Ideal.Quotient.mk _ (barp b)) = barr b := by
  apply (perfectPrismVarpiQuotientEquiv W hW).injective
  rw [RingEquiv.apply_symm_apply]
  exact (perfectPrismVarpiQuotientEquiv_mk W hW b).symm

/-- 概要：x mod p で係数還元した無限根環と R/ϖ 上の無限根環は環同型。
方針：係数商の交換と係数環同型のモノイド環への持上げを合成する。
規約：実際の係数主イデアル K による商を取る。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力台環の具体化。 -/
def perfectPrismVarpiRootInputEquiv : (N ⧸ K) ≃+* Nv :=
  (powerRootCoefficientQuotientEquiv R₀ p hp a).trans
    (AddMonoidAlgebra.mapRingEquiv G (perfectPrismVarpiQuotientEquiv W hW).symm)

/-- 概要：入力環同型は A 由来の単項式の係数を同じ R/ϖ 係数へ送る。
方針：商比較と係数同型の単項式公式を合成する。
規約：指数は変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力元の同定。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の多項式係数の照合。 -/
theorem perfectPrismVarpiRootInputEquiv_coeff (b : A) :
    perfectPrismVarpiRootInputEquiv W hW
      (Ideal.Quotient.mk K (algebraMap R₀ N (barp b))) =
        algebraMap Rv Nv (barr b) := by
  simpa [AddMonoidAlgebra.coe_algebraMap] using
    perfectPrismVarpiRootInputEquiv_single W hW 0 b

/-- 概要：入力環同型は全ての根変数を同じ番号の根変数へ送る。
方針：係数 1 の単項式の比較を使う。
規約：任意の段 n を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常変数での評価の比較。 -/
theorem perfectPrismVarpiRootInputEquiv_variable (n : ℕ) :
    perfectPrismVarpiRootInputEquiv W hW
      (Ideal.Quotient.mk K (powerRootPolynomialVariable R₀ p hp n)) =
        powerRootPolynomialVariable Rv p hp n := by
  simpa only [powerRootPolynomialVariable, map_one] using
    perfectPrismVarpiRootInputEquiv_single W hW (powerRootVariableExponent p hp n) 1

/-- 概要：名前付きモニック入力の係数還元は R/ϖ 上の同じ多項式の評価。
方針：評価の環射に関する自然性と係数・変数の照合を使う。
規約：等式にはモニック性を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の原典の f との同定。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の還元後の pd 入力。 -/
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

end PerfectPrismVarpiRootInput

/-! ## ϖ 還元した pd 表示環と原典の入力上の標準表示

## 概要

無限根環上の pd 表示環を x=φ⁻¹(d) の係数像で割った実商は、R/ϖ 上の無限根環の
同じ多項式入力の標準 pd 表示と環同型。BS 著者版 Remark 7.15(1)（著者版 p.62）の台環比較。

## 方針

一次関係商と係数商の交換同型を、無限根入力環の比較で誘導される表示環同型と合成する。
係数と全標準分冪生成元の像を計算する。

## 規約

通常環同型自体には prism 商の p 正則性もモニック性も要求しない。
prismatic envelope の Frobenius 引戻しとの同定はまだ含まない。

## 使われ方

構成済みの実分冪構造と普遍性を、原典の R/ϖ 係数上の標準台環へ移す。
-/

@[expose] public noncomputable section PerfectPrismVarpiPDComparison

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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の還元後の pd 包の同定。 -/
def perfectPrismVarpiPDEnvelopeEquiv : (D ⧸ K) ≃+* Dv :=
  principalDPReducedCoefficientEquiv (algebraMap R₀ N a) z (algebraMap R₀ D a)
    (IsScalarTower.algebraMap_apply R₀ N D a) (perfectPrismVarpiRootInputEquiv W hW)
    zv (perfectPrismVarpiRootInputEquiv_input W hW f)

/-- 概要：表示環比較は全標準分冪生成元の次数を保つ。
方針：二つの比較同型の生成元公式を合成する。
規約：次数零も含む。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実分冪構造の移送。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の係数代数としての比較。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実 pd 包の構造比較。 -/
theorem perfectPrismVarpiPDEnvelopeEquiv_input :
    perfectPrismVarpiPDEnvelopeEquiv W hW f
      (Ideal.Quotient.mk K (algebraMap N D z)) = algebraMap Nv Dv zv := by
  simpa only [principalDPGenerator_one] using
    perfectPrismVarpiPDEnvelopeEquiv_generator W hW f 1

/-- 概要：還元した正次数分冪イデアルは原典の入力の正次数イデアルに対応する。
方針：像の合成と生成集合の像を計算し、全標準生成元の対応を使う。
規約：イデアルの等式は実表示環同型の像として述べる。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実分冪構造の移送の入力。 -/
theorem perfectPrismVarpiPDEnvelopeEquiv_positiveIdeal :
    ((principalDPPositiveIdeal z).map (Ideal.Quotient.mk K)).map
      (perfectPrismVarpiPDEnvelopeEquiv W hW f).toRingHom = principalDPPositiveIdeal zv := by
  rw [Ideal.map_map, principalDPPositiveIdeal, Ideal.map_span, ← Set.range_comp']
  change Ideal.span (Set.range fun n : ℕ => perfectPrismVarpiPDEnvelopeEquiv W hW f
    (Ideal.Quotient.mk K (principalDPGenerator z (n + 1)))) = _
  simp only [perfectPrismVarpiPDEnvelopeEquiv_generator, principalDPPositiveIdeal]

end SerrePositivity.BhattScholze.Andre

end PerfectPrismVarpiPDComparison

/-! ## André R1：原典の R/ϖ 無限根環上の pd 比較の入口

## 概要

R/ϖ 上のモニック入力の実分冪構造と入力公式には、prism 商の p 正則性を要しない版を使う。
BS 著者版 Remark 7.15(1)（著者版 p.62）の台環・標準入力を保つ比較を読み込む。

## 方針

旧 hpR 付きの構造・入力公式を削除した。
無条件版は Unconditional.MonicPDEnvelope の射影的係数商による実構造を使い、集約から公開する。
原典の p ねじれなしへの帰着とは異なる線形切断・構造移送による経路。

## 規約

比較の台環・係数作用・正次数イデアルを保持する。
依存順序を保つため、この入口から後続の無条件版を import しない。

## 使われ方

旧ファイルの import 経路を保ち、標準表示の同型と一般の実 pd 普遍性を供給する。
-/

/-! ## 原典の係数環上の実 pd 包の切断表示と忠実平坦性

## 概要

R/ϖ 上の無限根環のモニック入力の同じ pd 表示環は、入力の p 乗商上の可算切断表示を
持ち、係数環上自由、入力が正次数なら忠実平坦となる。
BS 著者版 Remark 7.15(1)（著者版 p.62）の通常代数計算を原典の係数環に接続する。

## 方針

R/ϖ が p を殺すことを具体的な係数商同型から示す。
検証済みの切断表示同型と無限根モニック冪商の基底・忠実平坦性を同じ台環へ適用する。

## 規約

今回の環同型・加群の結果は prism 商の p 正則性を要求しない。
分冪値の公式は別ファイルの無条件版で提供する。

## 使われ方

原典の pd 包の通常平坦性計算を prismatic envelope との後続比較に供給する。
-/

@[expose] public noncomputable section PerfectPrismVarpiNativePDFlat

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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の標数 p の切断表示への入力。 -/
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
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の同じ表示環の切断表示。 -/
theorem perfectPrismVarpiRootRing_prime_eq_zero : (p : Nv) = 0 := by
  simpa only [map_natCast, map_zero] using
    congrArg (algebraMap Rv Nv) (perfectPrismVarpiCoefficient_prime_eq_zero W hW)

/-- 概要：原典係数上のモニック入力の pd 表示環は可算切断表示と代数同型。
方針：標数 p の標準表示同型を同じ入力台環へ適用する。
規約：入力の p 乗商の作用は既存の principalDPQuotientAlgebra を固定する。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の P/(f^p)[gᵢ]/(gᵢ^p) の表示。 -/
def perfectPrismVarpiNativePDEnvelope_truncatedEquiv (f : Polynomial A) :
    letI := principalDPQuotientAlgebra hp (perfectPrismVarpiRootRing_prime_eq_zero W hW) (zv f)
    (Dv f) ≃ₐ[Nv ⧸ Ideal.span {(zv f) ^ p}] PrincipalDPTruncatedPresentation p (zv f) :=
  principalDPTruncatedQuotientAlgEquiv p (perfectPrismVarpiRootRing_prime_eq_zero W hW) _

/-- 概要：原典係数上の pd 包は入力の p 乗商上自由。
方針：切断表示の基底を係数商上の同型で戻す。
規約：モニック性も正次数もこの係数商上の自由性には不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の明示切断表示の自由性。 -/
theorem perfectPrismVarpiNativePDEnvelope_free_over_powerQuotient (f : Polynomial A) :
    letI := principalDPQuotientAlgebra hp (perfectPrismVarpiRootRing_prime_eq_zero W hW) (zv f)
    Module.Free (Nv ⧸ Ideal.span {(zv f) ^ p}) (Dv f) :=
  principalDPPresentation_free_via_truncated p (perfectPrismVarpiRootRing_prime_eq_zero W hW) _

/-- 概要：原典係数上の同じモニック pd 包の台環は R/ϖ 上自由。
方針：通常モニック冪商と切断表示の自由性をスカラー塔で合成する既存の定理を使う。
規約：零係数環と定数モニック入力を含む。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常平坦性計算。 -/
theorem perfectPrismVarpiNativePDEnvelope_free (f : Polynomial A) (hf : f.Monic) :
    Module.Free Rv (Dv f) :=
  powerRootMonicDPPresentation_free Rv p hp (Fact.out : p.Prime)
    (perfectPrismVarpiCoefficient_prime_eq_zero W hW) (f.map barr) (hf.map barr)

/-- 概要：原典係数上の正次数モニック pd 包の台環は R/ϖ 上忠実平坦。
方針：非零係数環ではモニック次数保存、零係数環では加群の自明性を使う。
規約：正次数は元の多項式 f に要求する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の原典係数での忠実平坦性。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常代数計算の最初の自由性。 -/
theorem perfectPrismVarpiRootInput_free : Module.Free Rv Nv :=
  powerRootPolynomial_free Rv p hp

/-- 概要：原典のモニック入力の p 乗による実商は R/ϖ 上自由。
方針：モニック冪商の既存の基底を評価された入力の主イデアル商へ移す。
規約：正次数や prism 商の p 正則性は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の P/(f^p) の自由性。 -/
theorem perfectPrismVarpiRootPowerQuotient_free (f : Polynomial A) (hf : f.Monic) :
    Module.Free Rv (Nv ⧸ Ideal.span {(zv f) ^ p}) := by
  let := powerRootPolynomialBaseAlgebra Rv p hp
  have h := powerRootPolynomialPowerQuotient_free Rv p hp (f.map barr) (hf.map barr)
  change Module.Free Rv
    (Nv ⧸ (Ideal.span {(f.map barr) ^ p}).map (algebraMap (Polynomial Rv) Nv)) at h
  rw [powerRootPolynomialQuotient_ideal, map_pow] at h
  exact h


end SerrePositivity.BhattScholze.Andre

end PerfectPrismVarpiNativePDFlat
