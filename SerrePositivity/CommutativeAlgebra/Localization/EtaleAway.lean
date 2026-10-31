module

public import SerrePositivity.CommutativeAlgebra.GenericEtale
public import Mathlib.RingTheory.Localization.BaseChange

/-! # エタールな主局所化と基底変換

## 概要

`A_g → B_g` がエタールであることは `A` 上でエタールであることと同値（`Algebra.Etale.iff_of_isLocalizationAway`）。主局所化の上のエタール性は任意の基底変換で保たれ、有限表示なら (g) の元 x の主局所化へ移る。

## 方針

一般形は任意の `IsLocalization.Away` の模型の上で示す（Mathlib の形）。`awayAlgebra` を使う既存の 4 つの主張（`etale_away_baseChange` ほか）はその特殊化として名前と主張を残す（CLMST が型の中で使う）。

## 規約

一般形の `iff_of_isLocalizationAway` は提出候補。

## 使われ方

CLMST の Prop 2.4.7（エタールな階数の層別）、同種写像の降下。
-/

@[expose] public noncomputable section

universe u

section GeneralPart

open scoped TensorProduct

namespace SerrePositivity.EtaleAway

variable {A : Type*} [CommRing A] (g : A)
  (Ag Bg : Type*) [CommRing Ag] [CommRing Bg] [Algebra A Ag] [IsLocalization.Away g Ag]
  [Algebra A Bg] [Algebra Ag Bg] [IsScalarTower A Ag Bg]

include g in
/-- `A_g` 上でエタールであることと `A` 上でエタールであることは同値。 -/
theorem iff_of_isLocalizationAway : Algebra.Etale Ag Bg ↔ Algebra.Etale A Bg := by
  have : Algebra.Etale A Ag := Algebra.Etale.of_isLocalizationAway g
  exact ⟨fun _ => Algebra.Etale.comp A Ag Bg, fun _ => Algebra.Etale.of_restrictScalars A Ag Bg⟩

end SerrePositivity.EtaleAway

namespace SerrePositivity.EtaleAway

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (g : A)
  {Ag Bg : Type*} [CommRing Ag] [CommRing Bg] [Algebra A Ag] [IsLocalization.Away g Ag]
  [Algebra A Bg] [Algebra Ag Bg] [IsScalarTower A Ag Bg]
  [Algebra B Bg] [IsScalarTower A B Bg] [IsLocalization.Away (algebraMap A B g) Bg]
  (R : Type*) [CommRing R] [Algebra A R]
  (Rg Cg : Type*) [CommRing Rg] [CommRing Cg] [Algebra R Rg]
  [IsLocalization.Away (algebraMap A R g) Rg]
  [Algebra (R ⊗[A] B) Cg] [IsLocalization.Away (algebraMap R (R ⊗[A] B) (algebraMap A R g)) Cg]
  [Algebra R Cg] [IsScalarTower R (R ⊗[A] B) Cg] [Algebra Rg Cg] [IsScalarTower R Rg Cg]

include B g R in
/-- 主局所化の上のエタール性は基底変換で保たれる：`A_g → B_g` がエタールなら、`R_g → (R ⊗[A] B)_g`
もエタール。 -/
theorem away_baseChange (h : Algebra.Etale Ag Bg) : Algebra.Etale Rg Cg := by
  have : Algebra.Etale A Bg := (iff_of_isLocalizationAway g Ag Bg).mp h
  have heq : algebraMap R (R ⊗[A] B) (algebraMap A R g) = (1 : R) ⊗ₜ[A] algebraMap A B g := by
    rw [← IsScalarTower.algebraMap_apply A R (R ⊗[A] B), Algebra.TensorProduct.algebraMap_apply']
  have : IsLocalization
      ((Submonoid.powers (algebraMap A B g)).map
        (Algebra.TensorProduct.includeRight (R := A) (A := R))) Cg := by
    simp only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply, ← heq]
    infer_instance
  have : Algebra.Etale R Cg :=
    Algebra.Etale.of_equiv (IsLocalization.tensorProductEquivOfMapIncludeRight A R (.powers (algebraMap A B g)) Bg Cg)
  exact (iff_of_isLocalizationAway (algebraMap A R g) Rg Cg).mpr this

end SerrePositivity.EtaleAway

namespace SerrePositivity.EtaleAway

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
  (g x : A) (hx : x ∈ Ideal.span {g})
  {Ag Bg : Type*} [CommRing Ag] [CommRing Bg] [Algebra A Ag] [IsLocalization.Away g Ag]
  [Algebra A Bg] [Algebra Ag Bg] [IsScalarTower A Ag Bg]
  [Algebra B Bg] [IsScalarTower A B Bg] [IsLocalization.Away (algebraMap A B g) Bg]
  (Ax Bx : Type*) [CommRing Ax] [CommRing Bx] [Algebra A Ax] [IsLocalization.Away x Ax]
  [Algebra A Bx] [Algebra Ax Bx] [IsScalarTower A Ax Bx]
  [Algebra B Bx] [IsScalarTower A B Bx] [IsLocalization.Away (algebraMap A B x) Bx]

include B hx in
/-- 有限表示な代数で `A_g → B_g` がエタールなら、`(g)` の元 `x` についても `A_x → B_x` はエタール。 -/
theorem away_of_mem_span_singleton (h : Algebra.Etale Ag Bg) : Algebra.Etale Ax Bx := by
  have : Algebra.Etale A Bg := (iff_of_isLocalizationAway g Ag Bg).mp h
  have hopen : (PrimeSpectrum.basicOpen (algebraMap A B x) : Set (PrimeSpectrum B)) ⊆
      PrimeSpectrum.basicOpen (algebraMap A B g) := by
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul]
    exact PrimeSpectrum.basicOpen_mul_le_left _ _
  have hg : Algebra.Etale A (Localization.Away (algebraMap A B g)) :=
    Algebra.Etale.of_equiv (IsLocalization.algEquiv (.powers (algebraMap A B g)) Bg _ |>.restrictScalars A)
  have hx' : Algebra.Etale A (Localization.Away (algebraMap A B x)) :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.mp (hopen.trans
      (Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr hg))
  have : Algebra.Etale A Bx :=
    Algebra.Etale.of_equiv (IsLocalization.algEquiv (.powers (algebraMap A B x)) (Localization.Away (algebraMap A B x)) Bx |>.restrictScalars A)
  exact (iff_of_isLocalizationAway x Ax Bx).mpr this

end SerrePositivity.EtaleAway

end GeneralPart

section EtaleAwayBaseChangePart

namespace SerrePositivity.GenericEtale
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

variable (A R B : Type u) [CommRing A] [CommRing R] [CommRing B]
    [Algebra A R] [Algebra A B]

/-- 標準局所化後のエタール性は、任意の基底変更により保たれる。
両側の局所化上の作用は awayAlgebra で明示する。 -/
theorem etale_away_baseChange (g : A) :
    let _ := awayAlgebra A B g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A B g)) →
      let _ := awayAlgebra R (R ⊗[A] B) (algebraMap A R g)
      Algebra.Etale (Localization.Away (algebraMap A R g))
        (Localization.Away (algebraMap R (R ⊗[A] B) (algebraMap A R g))) := by
  let := awayAlgebra A B g
  dsimp only
  intro h
  have := awayAlgebra_scalarTower A B g
  let := awayAlgebra R (R ⊗[A] B) (algebraMap A R g)
  have := awayAlgebra_scalarTower R (R ⊗[A] B) (algebraMap A R g)
  exact EtaleAway.away_baseChange (A := A) (B := B) g R (Localization.Away (algebraMap A R g))
    (Localization.Away (algebraMap R (R ⊗[A] B) (algebraMap A R g))) h

/-- 有限表示な代数では、g の局所化上のエタール性は (g) の各元の局所化へ移る。
basicOpen(x)⊆basicOpen(g) を使い、エタール軌跡の判定から導く。 -/
theorem etale_away_of_mem_span_singleton
    (R₀ S : Type u) [CommRing R₀] [CommRing S] [Algebra R₀ S]
    [Algebra.FinitePresentation R₀ S] (g x : R₀) (hx : x ∈ Ideal.span {g}) :
    let _ := awayAlgebra R₀ S g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R₀ S g)) →
      let _ := awayAlgebra R₀ S x
      Algebra.Etale (Localization.Away x) (Localization.Away (algebraMap R₀ S x)) := by
  let := awayAlgebra R₀ S g
  dsimp only
  intro h
  have := awayAlgebra_scalarTower R₀ S g
  let := awayAlgebra R₀ S x
  have := awayAlgebra_scalarTower R₀ S x
  exact EtaleAway.away_of_mem_span_singleton (A := R₀) (B := S) g x hx (Localization.Away x)
    (Localization.Away (algebraMap R₀ S x)) h

/-- 基底変更後、像 g が生成する主イデアルの全ての元の反転後にエタールとなる。
有限表示性だけを追加し、任意の基底変更 R に平坦性や Noether 性を要求しない。 -/
theorem etale_away_baseChange_of_mem_span_singleton [Algebra.FinitePresentation A B]
    (g : A) (x : R) (hx : x ∈ Ideal.span {algebraMap A R g}) :
    let _ := awayAlgebra A B g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A B g)) →
      let _ := awayAlgebra R (R ⊗[A] B) x
      Algebra.Etale (Localization.Away x)
        (Localization.Away (algebraMap R (R ⊗[A] B) x)) := by
  let := awayAlgebra A B g
  dsimp only
  intro h
  exact etale_away_of_mem_span_singleton R (R ⊗[A] B) (algebraMap A R g) x hx
    (etale_away_baseChange A R B g h)

end SerrePositivity.GenericEtale

end EtaleAwayBaseChangePart

section EtaleAwayTensorBaseChangePart

namespace SerrePositivity
open scoped TensorProduct

/-- Preserve the KL entry point using the existing general base change theorem.
The source and target use their specified standard localization algebras. -/
theorem etaleAway_tensor_baseChange
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (g : R) :
    letI := GenericEtale.awayAlgebra R A g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)) →
      letI := GenericEtale.awayAlgebra B (B ⊗[R] A) (algebraMap R B g)
      Algebra.Etale (Localization.Away (algebraMap R B g))
        (Localization.Away (algebraMap B (B ⊗[R] A) (algebraMap R B g))) :=
  GenericEtale.etale_away_baseChange R B A g

end SerrePositivity

end EtaleAwayTensorBaseChangePart
