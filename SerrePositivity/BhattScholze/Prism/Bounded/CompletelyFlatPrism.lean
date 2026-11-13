module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletelyFlat.Discrete
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletelyFlat.Discrete
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatReduction
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.PowerTorsion
import all SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatReduction
import SerrePositivity.HomologicalAlgebra.DerivedQuotientBaseChange

/-!
# 完全平坦な δ 代数の有界 prism

## 概要
有界 prism 上の完全平坦な導来完備 δ 代数は、基底生成元の像を向きとする有界 prism をなす。

## 方針
完全平坦性を離散な導来対象に移し、生成元剰余の離散性から正則性と有界性を得る。

## 規約
BS 著者版 Lemma 3.7 (3)。二つの主元による導来完備性を用いる。

## 使われ方
有界 prism の平坦な押し出し。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open CategoryTheory CategoryTheory.Limits DerivedCompletion
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra

variable {A : Type u} [CommRing A]

/-- 概要：完全平坦で導来完備な δ 代数に有界 prism の構造が入る。
方針：生成元剰余の離散性で正則性を、剰余のホモロジーの p 冪ねじれから有界性を得る。
規約：BS 著者版 Lemma 3.7 (3) の対象の対応。基底射と向きを指定する。
使われ方：完全平坦な底変換で有界 prism を作る。 -/
theorem exists_boundedPrism_of_completelyFlat_deltaAlgebra {p : ℕ} [Fact p.Prime]
    (P : OrientedPrism p A) (hP : IsBoundedPrism P)
    {B : Type u} [CommRing B] (δB : DeltaStructure p B) (f : A →+* B)
    (hf : P.deltaStructure.IsDeltaHom δB f)
    (hBp : IsModuleComplete B (p : B) (ModuleCat.of B B))
    (hBd : IsModuleComplete B (f P.generator) (ModuleCat.of B B))
    (hflat : letI := f.toAlgebra; IsCompletelyFlat (Ideal.span {(p : A), P.generator}) B) :
    ∃ (Q : OrientedPrism p B) (g : OrientedPrism.Hom P Q),
      Q.deltaStructure = δB ∧ Q.generator = f P.generator ∧ g.toRingHom = f ∧ IsBoundedPrism Q := by
  let := f.toAlgebra
  let d := P.generator
  let I := Ideal.span {(p : A), d}
  let M := ModuleCat.of A B
  let X := boundedAboveDerivedSingleFunctor.obj M
  have hcA (a : A) (ha : IsModuleComplete B (f a) (ModuleCat.of B B)) :
      IsComplete A a X.obj :=
    (isModuleComplete_algebraMap_iff A B a B).mp ha
  have hc := hcA (p : A) (by simpa only [map_natCast] using hBp)
  have ht := discrete_completelyFlat I M hflat
  have red := derivedGeneratorPowerReduction_pure_bounded P hP X hc ht 1
  obtain ⟨hGE, hLE, hbound⟩ := red
  let d₁ := P.generator ^ (1 : ℕ)
  have hd₁ : d₁ = d := pow_one _
  have hregA : IsSMulRegular A d := P.generator_regular
  have hregH₁ := (derived_pure_of_complete_regular_quotient_pure d₁ (hregA.pow 1) X
    (hcA d₁ (by rw [hd₁]; exact hBd)) (fun i hi ↦ by
      rcases lt_or_gt_of_ne hi with hi | hi
      · let := hGE
        exact DerivedCategory.isZero_of_isGE _ 0 i hi
      · let := hLE
        exact DerivedCategory.isZero_of_isLE _ 0 i hi)).2.2
  have hregH : IsSMulRegular ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj X.obj) d :=
    hd₁ ▸ hregH₁
  let e : M ≃ₗ[A] ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj X.obj) :=
    ((realizedSingleH0Iso A).app M).symm.toLinearEquiv
  have hreg : Function.Injective (f d * ·) := by
    intro x y hxy
    apply e.injective
    apply hregH
    change d • e x = d • e y
    rw [← e.map_smul, ← e.map_smul]
    exact congrArg e hxy
  let Q := OrientedPrism.ofDistinguished δB (f d) (hf.map_isDistinguished P.isDistinguished_generator)
    hreg hBp hBd
  let g : OrientedPrism.Hom P Q := ⟨f, hf, by
    rw [OrientedPrism.ideal, Ideal.span_le]
    exact Set.singleton_subset_iff.mpr (Ideal.subset_span rfl)⟩
  refine ⟨Q, g, rfl, rfl, rfl, ?_⟩
  let J := Ideal.span {d₁}
  let q := Ideal.Quotient.mk J
  have hJ : scalarExtensionTorVanishing q M :=
    scalarExtensionTorVanishing_principal_pow_of_regular d hregA M hreg 1
  have hmap : J.map (algebraMap A B) = Q.ideal := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {f d₁} = Ideal.span {f d}
    rw [hd₁]
  let e₁ := DerivedCategory.Minus.ι.mapIso (derivedQuotientAlgebraIso J B hJ)
  let e₂ := (DerivedCategory.homologyFunctor (ModuleCat (A ⧸ J)) 0).mapIso e₁ ≪≫
    (realizedSingleH0Iso (A ⧸ J)).app (ModuleCat.of (A ⧸ J) (B ⧸ J.map (algebraMap A B)))
  let l := e₂.toLinearEquiv
  have hbound' : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ J.map (algebraMap A B),
      (p : _) ^ n * x = 0 → (p : _) ^ N * x = 0 := by
    obtain ⟨N, hN⟩ := hbound
    have he (k : ℕ) (x : B ⧸ J.map (algebraMap A B)) :
        (q (p : A)) ^ k • x = (p : _) ^ k * x := by
      rw [Algebra.smul_def, map_pow, map_natCast, map_natCast]
    refine ⟨N, fun n x hx ↦ ?_⟩
    have hz := hN n (l.symm x) (by rw [← l.symm.map_smul, he n, hx, map_zero])
    have hz' := congrArg l hz
    rw [← he N]
    simpa only [map_smul, LinearEquiv.apply_symm_apply, map_zero] using hz'
  rw [IsBoundedPrism, ← hmap]
  exact hbound'

end SerrePositivity.BhattScholze.Prismatic

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 3.7" (partial := special) "(1) と (2)（完全平坦な複体の離散性、通常の導来圏で、BS-W15 K4）、(3)（完全平坦な δ 代数から有界 prism、exists_boundedPrism_of_completelyFlat_deltaAlgebra）は本体。(4) は不要（D19）。向き付きの基底 ／ 11-11 更新（2） ／ 11-12 夜更新（ノート本文の更新時）"] _root_.SerrePositivity.BhattScholze.Prismatic.exists_boundedPrism_of_completelyFlat_deltaAlgebra
