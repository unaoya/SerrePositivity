module

public import SerrePositivity.BhattScholze.Delta.Division.Basic
public import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaRing
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensor
public import SerrePositivity.BhattScholze.Prism.Basic.Bounded
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RepeatedCoordinate

/-!
# Construction 6.1 の結晶被覆の環と標準射

## 概要
φ(d)/p の δ 除算の p 冪ねじれ除去商を p 完備化し、生成元 p の prism と Frobenius で捻った標準射を作る。

## 方針
既存のねじれ除去商の p 正則性を (p,p) 完備化に移す。

## 規約
BS 著者版 Construction 6.1 のねじれ除去による環模型。生の除算包との比較には剰余の p 正則性を使う。

## 使われ方
Construction 6.1 の明示的な完全平坦性入力の下での剰余比較・保存性・Tor 振幅。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze.Prismatic.Construction61

open DerivedCompletion

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-- φ(d)/p の添加後の p 冪ねじれ除去商。 -/
abbrev coverDivision := DeltaDivisionTorsionQuotient P.deltaStructure (p : A)
  (fun _ : Unit => P.deltaStructure.frobeniusLift P.generator)

/-- ねじれ除去商の既存の δ 構造。 -/
abbrev coverDivisionDelta := deltaDivisionTorsionStructure P.deltaStructure (p : A)
  (fun _ : Unit => P.deltaStructure.frobeniusLift P.generator)

/-- ねじれ除去商への係数射。 -/
abbrev coverDivisionMap := deltaDivisionTorsionMap P.deltaStructure (p : A)
  (fun _ : Unit => P.deltaStructure.frobeniusLift P.generator)

/-- Construction 6.1 の (p,p) 完備化による環模型。 -/
abbrev crystallineCoverRing := PDCompletionH0 (coverDivision P) p (p : coverDivision P)

instance : CommRing (crystallineCoverRing P) := pdCompletionCommRing _ p _

/-- 完備化の標準単位。 -/
abbrev coverUnit := pdCompletionUnit (coverDivision P) p (p : coverDivision P)

/-- 被覆の δ 構造。 -/
abbrev coverDelta := deltaPDCompletionStructure (coverDivisionDelta P) (p : coverDivision P)

/-- 被覆への自然な係数射。 -/
abbrev coverBase : A →+* crystallineCoverRing P := (coverUnit P).comp (coverDivisionMap P)

/-- 概要：ねじれ除去模型の実完備化でも p は正則。
方針：既存の商の p 正則性を繰り返した座標の比較で移す。
規約：BS 著者版 Construction 6.1 の環模型についての性質。
使われ方：結晶 prism の生成元の正則性。 -/
theorem crystallineCover_p_regular :
    Function.Injective (fun x : crystallineCoverRing P => (p : crystallineCoverRing P) * x) := by
  have hR : IsSMulRegular (coverDivision P) (p : coverDivision P) :=
    deltaDivisionTorsionQuotient_p_mul_injective P.deltaStructure _
  have h := pairCompletionRepeated_regular (coverDivision P) (p : coverDivision P) hR
  have hh : Function.Injective (fun x : crystallineCoverRing P =>
      coverUnit P (p : coverDivision P) * x) := h
  intro x y hxy
  apply hh
  have hcast : coverUnit P (p : coverDivision P) = (p : crystallineCoverRing P) :=
    map_natCast (coverUnit P) p
  rw [hcast]
  exact hxy

/-- 概要：被覆の環は自身の p 作用について導来完備。
方針：二座標完備化の第一座標の完備性を使う。
規約：BS 著者版 Construction 6.1。
使われ方：結晶 prism の二つの完備性。 -/
theorem crystallineCover_complete_p :
    IsModuleComplete (crystallineCoverRing P) (p : crystallineCoverRing P)
      (ModuleCat.of (crystallineCoverRing P) (crystallineCoverRing P)) :=
  pdCompletionH0_self_complete_p (coverDivision P) p (p : coverDivision P)

/-- 概要：ねじれ除去した完備環に生成元 p の結晶 prism を付ける。
方針：p 正則性・p 完備性と自明な p のイデアル包含を使う。
規約：BS 著者版 Construction 6.1。台環は指定した (p,p) 完備化。
使われ方：一般の向き付き prism からの Frobenius で捻った射。 -/
def crystallineCover : OrientedPrism p (crystallineCoverRing P) where
  deltaStructure := coverDelta P
  generator := p
  generator_regular := crystallineCover_p_regular P
  complete_p := crystallineCover_complete_p P
  complete_generator := crystallineCover_complete_p P
  p_mem := Ideal.subset_span (Set.mem_insert _ _)

/-- 被覆の生成元は p。 -/
@[simp] theorem crystallineCover_generator : (crystallineCover P).generator = p := rfl

/-- 概要：自然な係数射は δ 構造と両立する。
方針：ねじれ除去商と完備化の標準射の δ 両立を合成する。
規約：BS 著者版 Construction 6.1 の自然な A 代数構造。
使われ方：Frobenius で捻った prism 射の構成。 -/
theorem coverBase_isDeltaHom : P.deltaStructure.IsDeltaHom (coverDelta P) (coverBase P) :=
  (pdCompletionUnit_isDeltaHom (coverDivisionDelta P) (p : coverDivision P)).comp
    (deltaDivisionTorsionMap_isDeltaHom P.deltaStructure (p : A) _)

/-- 概要：Frobenius で捻った係数射は d を (p) に送る。
方針：φ(d) を p で割る既存の関係を標準完備化に送る。
規約：BS 著者版 Construction 6.1 の α のイデアル条件。
使われ方：prism 射 α の構成。 -/
theorem coverBase_frobenius_generator_mem :
    coverBase P (P.deltaStructure.frobeniusLift P.generator) ∈ (crystallineCover P).ideal := by
  apply Ideal.mem_span_singleton.mpr
  obtain ⟨t, ht⟩ := deltaDivisionTorsionMap_dvd P.deltaStructure (p : A)
    (fun _ : Unit => P.deltaStructure.frobeniusLift P.generator) ()
  refine ⟨coverUnit P t, ?_⟩
  change coverUnit P (coverDivisionMap P (P.deltaStructure.frobeniusLift P.generator)) =
    (p : crystallineCoverRing P) * coverUnit P t
  simpa only [map_mul, map_natCast] using congrArg (coverUnit P) ht

/-- 概要：α は自然な係数射と Frobenius の合成による prism 射。
方針：二つの δ 射を合成し、生成元の像の包含を使う。
規約：BS 著者版 Construction 6.1 の α。
使われ方：mod p の分解と導来完備底変換。 -/
def crystallineCoverMap : OrientedPrism.Hom P (crystallineCover P) where
  toRingHom := (coverBase P).comp P.deltaStructure.frobeniusLift
  map_delta := (coverBase_isDeltaHom P).comp P.deltaStructure.isDeltaHom_frobeniusLift_general
  ideal_le := by
    rw [OrientedPrism.ideal, Ideal.span_le]
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact coverBase_frobenius_generator_mem P

/-- 概要：結晶被覆は有界。
方針：p で割った商では p 自身が零である。
規約：BS 著者版 Construction 6.1 の結晶 prism の有界性。
使われ方：有界 prismatic site と比較の標的。 -/
theorem crystallineCover_bounded : IsBoundedPrism (crystallineCover P) := by
  refine ⟨1, fun n x hx => ?_⟩
  have hp : (p : crystallineCoverRing P ⧸ (crystallineCover P).ideal) = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self (p : crystallineCoverRing P))
    simpa only [map_natCast] using h
  simp only [pow_one, hp, zero_mul]

end SerrePositivity.BhattScholze.Prismatic.Construction61
