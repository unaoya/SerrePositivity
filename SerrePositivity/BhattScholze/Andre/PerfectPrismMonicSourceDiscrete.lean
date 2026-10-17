module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticSourcePowerInputs
public import SerrePositivity.BhattScholze.PerfectOrientedPrism
public import SerrePositivity.BhattScholze.DistinguishedPowerTorsion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteFlatReductionBounded
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteScalarConePurity
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology

/-!
# André E1・E2：完全 prism 上の有限モニック族の実完備化源の離散性

## 概要

完全 prism 上の有限正次数モニック族の一般 f/d 源を p,d の順に実導来完備化すると離散的となる。
BS Rem 7.15（著者版 p.62）の実 prismatic envelope 比較への入力。

## 方針

完全 prism の生成元冪商の p 冪ねじれ上界と、標準 mod p 還元の離散・平坦性から G9 を適用する。
その生成元商の離散性と d 導来完備性から元の対象の純性を得る。
原典の Prop 7.11 を用いる証明とは異なる経路の計算。

## 規約

有限全列挙と正次数モニック性を要求する。最終 perfectoid 商との環同型は別工程。

## 使われ方

同じ実 H⁰ を raw PD 完備化環へ比較して、元の係数射の完全忠実平坦性を導く。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
variable {m : ℕ} (s : Fin m ≃ σ)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "X" => MonicPrismaticSourceIteratedPDCompletion D d f
include hP hf hdeg s

/-- 概要：完全 prism 上の有限モニック族の実完備化源の正の生成元冪商は離散的。
方針：標準 mod p の離散・平坦性、p 導来完備性、生成元冪商の p 冪ねじれ上界を G9 へ渡す。
規約：d mod p の正則性は仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の元の実完備化対象の離散性。 -/
theorem perfectPrismMonicSourcePower_pure (n : ℕ) (hn : 0 < n) :
    let Z := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X
    Z.obj.IsGE 0 ∧ Z.obj.IsLE 0 := by
  let T := A ⧸ Ideal.span {d ^ n}
  let Z := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X
  obtain ⟨v, hv⟩ := P.isDistinguished_of_perfect hP
  obtain ⟨hc, hz, hflat⟩ := monicPrismaticSourceGeneratorPower_G9_inputs D d f n hn
    hf hdeg s hP.p_mul_injective P.generator_regular v hv
  have hbound : ∃ N : ℕ, ∀ k : ℕ, ∀ x : T,
      (p : T) ^ k * x = 0 → (p : T) ^ N * x = 0 := by
    let := P.isAdicComplete_p_of_perfect hP
    exact ⟨n, fun k x hx => hP.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow
      (P.isDistinguished_of_perfect hP) n k x hx⟩
  exact derived_pure_of_complete_flat_reduction (p : T) Z hz hflat hbound hc

/-- 概要：完全 prism 上の有限モニック族の実逐次 p,d 完備化源は離散的。
方針：生成元商の離散性、生成元の正則性、d 導来完備性を一般純性判定へ渡す。
規約：同じ元の係数環上の実対象を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ を環候補へ比較する。 -/
theorem perfectPrismMonicSource_pure : (X).obj.IsGE 0 ∧ (X).obj.IsLE 0 := by
  have hmod (i : ℤ) (hi : i ≠ 0) : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {d})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).obj X).obj) := by
    have hpow := perfectPrismMonicSourcePower_pure P hP f hf hdeg s 1 (by omega)
    dsimp only at hpow
    rw [pow_one] at hpow
    rcases lt_or_gt_of_ne hi with h | h
    · exact (DerivedCategory.isGE_iff _ _).mp hpow.1 i h
    · exact (DerivedCategory.isLE_iff _ _).mp hpow.2 i h
  obtain ⟨hGE, hLE, _⟩ := derived_pure_of_complete_regular_quotient_pure d
    P.generator_regular X (monicPrismaticSourceIteratedPDCompletion_isComplete_d D d f) hmod
  exact ⟨hGE, hLE⟩

/-- 概要：同じ実逐次完備化源の全非零次数ホモロジーは零。
方針：純性を標準 t 構造のホモロジー消滅として展開する。
規約：全非零整数次数を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数射の実還元計算への接続。 -/
theorem perfectPrismMonicSource_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj (X).obj) := by
  obtain ⟨hGE, hLE⟩ := perfectPrismMonicSource_pure P hP f hf hdeg s
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- 概要：実完備化源は同じ実 H⁰ の single と正規化された同型を持つ。
方針：標準 t 構造の純対象の既存正規化比較を使う。
規約：元の A 作用と実 H⁰ を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の raw PD 環との比較へ渡す。 -/
def perfectPrismMonicSourceSingleIso :
    (X).obj ≅ (DerivedCategory.singleFunctor (ModuleCat A) 0).obj
      ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (X).obj) := by
  obtain ⟨hGE, hLE⟩ := perfectPrismMonicSource_pure P hP f hf hdeg s
  let := hGE
  let := hLE
  exact normalizedPureHomologyIso (X).obj 0

end SerrePositivity.BhattScholze.Andre
