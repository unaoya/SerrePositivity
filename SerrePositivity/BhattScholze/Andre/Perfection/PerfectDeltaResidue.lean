module

public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrismaticResidue
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedRestriction
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence

/-!
# 完全な係数の Frobenius 各段の prism 剰余

## 概要
完全係数 δ 環の Frobenius 反復の各段における prism 係数商の同定と、Frobenius 係数制限による射影モデルの移送。
BS 著者版 Lemma 3.9 の完全化に使う、完全な係数の Frobenius 各段の prism 剰余を比較する。

## 方針
p を消す環射の下での Frobenius 反復の計算。

## 規約
原典に項目のない道具。

## 使われ方
André の一段の拡大。
-/

universe u v

/-! ## 完全係数δ環のFrobenius各段における正確なprism係数商 -/

@[expose] public noncomputable section PerfectDeltaPrismaticResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A)

/-- pを消す任意の通常射の下で、実Frobenius反復はpⁿ乗として作用する。 -/
theorem map_frobeniusLift_iterate_of_map_p_eq_zero {T : Type v} [CommRing T]
    (f : A →+* T) (hp : f (p : A) = 0) (x : A) (n : ℕ) :
    f ((D.frobeniusLift ^ n) x) = f x ^ (p ^ n) := by
  change f ((D.frobeniusLift : A → A)^[n] x) = _
  induction n with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, pow_one]
  | succ n ih =>
      rw [Function.iterate_succ_apply', D.map_frobeniusLift_of_map_p_eq_zero f hp, ih,
        Nat.pow_succ, pow_mul]

/-- Frobenius反復で動かした生成元の実(p,d)イデアルは、元の生成元のpⁿ冪のもの。 -/
theorem frobeniusPrismaticResidueIdeal_eq (d : A) (n : ℕ) :
    Ideal.span {(p : A), (D.frobeniusLift ^ n) d} =
      Ideal.span {(p : A), d ^ (p ^ n)} := by
  have he (J : Ideal A) (hp : (p : A) ∈ J) :
      Ideal.Quotient.mk J ((D.frobeniusLift ^ n) d) =
        Ideal.Quotient.mk J (d ^ (p ^ n)) := by
    rw [map_pow]
    exact map_frobeniusLift_iterate_of_map_p_eq_zero D (Ideal.Quotient.mk J)
      (Ideal.Quotient.eq_zero_iff_mem.mpr hp) d n
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [he _ (Ideal.subset_span (by simp))]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← he _ (Ideal.subset_span (by simp))]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/-- 完全係数δ環の実φⁿが誘導する、移動した生成元を用いた商環同型。 -/
def perfectDeltaFrobeniusPrismaticResidueEquiv (hD : D.IsPerfect) (d : A) (n : ℕ) :
    (A ⧸ Ideal.span {(p : A), d}) ≃+*
      (A ⧸ Ideal.span {(p : A), (D.frobeniusLift ^ n) d}) :=
  Ideal.quotientEquiv _ _ (RingEquiv.ofBijective (D.frobeniusLift ^ n) (hD.iterate n))
    (by rw [Ideal.map_span, Set.image_pair, map_natCast]; rfl)

/-- 移動した生成元の商同型は、元環の標準φⁿ係数像を保つ。 -/
theorem perfectDeltaFrobeniusPrismaticResidueEquiv_mk
    (hD : D.IsPerfect) (d : A) (n : ℕ) (x : A) :
    perfectDeltaFrobeniusPrismaticResidueEquiv D hD d n
      (Ideal.Quotient.mk (Ideal.span {(p : A), d}) x) =
        Ideal.Quotient.mk _ ((D.frobeniusLift ^ n) x) := rfl

/-- 同じ実φⁿの係数商を、冪零還元からの純性・平坦性の判定に使う正確なA/(p,d^(pⁿ))へ比較する。 -/
def perfectDeltaFrobeniusPowerResidueEquiv (hD : D.IsPerfect) (d : A) (n : ℕ) :
    (A ⧸ Ideal.span {(p : A), d}) ≃+*
      (A ⧸ Ideal.span {(p : A), d ^ (p ^ n)}) :=
  (perfectDeltaFrobeniusPrismaticResidueEquiv D hD d n).trans
    (Ideal.quotEquivOfEq (frobeniusPrismaticResidueIdeal_eq D d n))

/-- 冪剰余への比較も、元環の実φⁿ係数像を保つ。 -/
theorem perfectDeltaFrobeniusPowerResidueEquiv_mk
    (hD : D.IsPerfect) (d : A) (n : ℕ) (x : A) :
    perfectDeltaFrobeniusPowerResidueEquiv D hD d n
      (Ideal.Quotient.mk (Ideal.span {(p : A), d}) x) =
        Ideal.Quotient.mk _ ((D.frobeniusLift ^ n) x) := by
  rw [perfectDeltaFrobeniusPowerResidueEquiv, RingEquiv.trans_apply,
    perfectDeltaFrobeniusPrismaticResidueEquiv_mk, Ideal.quotEquivOfEq_mk]

end SerrePositivity.BhattScholze

end PerfectDeltaPrismaticResidue

/-! ## 実Frobenius係数制限による射影モデルの移送 -/

@[expose] public noncomputable section PerfectDeltaFrobeniusModels

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (hD : D.IsPerfect) (n : ℕ)
local notation "e" => RingEquiv.ofBijective (D.frobeniusLift ^ n) (hD.iterate n)
local notation "F" => ModuleCat.restrictScalars (RingEquiv.toRingHom e)

/-- 実φⁿの係数制限は、環同値による圏同値として射影加群を保つ。 -/
theorem perfectDeltaFrobeniusRestrict_projective (M : ModuleCat.{u} A) [Projective M] :
    Projective ((F).obj M) := by
  let : (F).IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  exact (F).projective_obj_of_projective inferInstance

/-- 指定した実射影モデルを、実φⁿ係数制限対象の射影モデルへ移す。 -/
def perfectDeltaFrobeniusRestrictModel
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) (P : BoundedAboveDerivedModel X.obj) :
    BoundedAboveDerivedModel
      (((boundedAboveDerivedRestrictScalars (e).toRingHom).obj X).obj) where
  complex := ((F).mapHomologicalComplex (.up ℤ)).obj P.complex
  bound := P.bound
  bounded := inferInstance
  projective i := perfectDeltaFrobeniusRestrict_projective D hD n (P.complex.X i)
  iso := (boundedAboveDerivedRestrictScalarsModelIso (e).toRingHom X P).symm

/-- 元の係数イデアルによる実還元は、移した同じ射影モデルで計算できる。 -/
def perfectDeltaFrobeniusRestrictQuotientModelIso (I : Ideal A)
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) (P : BoundedAboveDerivedModel X.obj) :
    ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj
      ((boundedAboveDerivedRestrictScalars (e).toRingHom).obj X)).obj ≅
        DerivedCategory.Q.obj (baseChange (Ideal.Quotient.mk I)
          (((F).mapHomologicalComplex (.up ℤ)).obj P.complex)) :=
  boundedAboveDerivedBaseChangeModelIso (Ideal.Quotient.mk I) _
    (perfectDeltaFrobeniusRestrictModel D hD n X P)

end SerrePositivity.BhattScholze

end PerfectDeltaFrobeniusModels

/-! ## 実Frobenius係数制限とprism係数商の導来可換図式 -/

@[expose] public noncomputable section PerfectDeltaFrobeniusQuotientSquare

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (n : ℕ)
local notation "e" => RingEquiv.ofBijective (D.frobeniusLift ^ n) (hD.iterate n)
local notation "κ" => perfectDeltaFrobeniusPrismaticResidueEquiv D hD d n
local notation "I₀" => Ideal.span {(p : A), d}
local notation "Jₙ" => Ideal.span {(p : A), (D.frobeniusLift ^ n) d}
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "qₙ" => Ideal.Quotient.mk Jₙ

/-- 逆Frobeniusと実標準商射の係数図式。 -/
theorem perfectDeltaFrobeniusQuotient_inverse_square :
    (q₀).comp (e).symm.toRingHom = (κ).symm.toRingHom.comp qₙ := by
  apply RingHom.ext
  intro x
  rfl

/-- 実φⁿ制限後の標準係数拡大と、移動した商への拡大後の正確な係数制限の比較。 -/
def perfectDeltaFrobeniusQuotientScalarIso :
    ModuleCat.restrictScalars (e).toRingHom ⋙ ModuleCat.extendScalars q₀ ≅
      ModuleCat.extendScalars qₙ ⋙ ModuleCat.restrictScalars (κ).toRingHom :=
  Functor.isoWhiskerRight (restrictScalarsIsoExtendInverse e) (ModuleCat.extendScalars q₀) ≪≫
    (ModuleCat.extendScalarsComp (e).symm.toRingHom q₀).symm ≪≫
    eqToIso (congrArg ModuleCat.extendScalars
      (perfectDeltaFrobeniusQuotient_inverse_square D hD d n)) ≪≫
    ModuleCat.extendScalarsComp qₙ (κ).symm.toRingHom ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars qₙ) (restrictScalarsIsoExtendInverse κ).symm

/-- 同じ通常関手squareを、実際の射影複体の各項へ適用する。 -/
def perfectDeltaFrobeniusQuotientCochainIso (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    baseChange q₀
      (((ModuleCat.restrictScalars (e).toRingHom).mapHomologicalComplex (.up ℤ)).obj K) ≅
        ((ModuleCat.restrictScalars (κ).toRingHom).mapHomologicalComplex (.up ℤ)).obj
          (baseChange qₙ K) :=
  (Functor.mapHomologicalComplexCompIso
    (perfectDeltaFrobeniusQuotientScalarIso D hD d n) (.up ℤ)).app K

/-- 指定した同じ実射影モデル上で、Frobeniusねじれ源の実係数商還元を計算する。 -/
def perfectDeltaFrobeniusQuotientDerivedIso
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) (P : BoundedAboveDerivedModel X.obj) :
    (boundedAboveDerivedBaseChange q₀).obj
      ((boundedAboveDerivedRestrictScalars (e).toRingHom).obj X) ≅
        (boundedAboveDerivedRestrictScalars (κ).toRingHom).obj
          ((boundedAboveDerivedBaseChange qₙ).obj X) :=
  ObjectProperty.isoMk _
    (perfectDeltaFrobeniusRestrictQuotientModelIso D hD n I₀ X P ≪≫
      DerivedCategory.Q.mapIso (perfectDeltaFrobeniusQuotientCochainIso D hD d n P.complex) ≪≫
        ((derivedRestrictScalarsFactors (κ).toRingHom).app
          (baseChange qₙ P.complex)).symm ≪≫
        (derivedRestrictScalars (κ).toRingHom).mapIso
          (boundedAboveDerivedBaseChangeModelIso qₙ X P).symm)

end SerrePositivity.BhattScholze

end PerfectDeltaFrobeniusQuotientSquare
