module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prism.Bounded.CompleteFlatReduction
public import SerrePositivity.CommutativeAlgebra.Adic.ModuleCompleteSup
import SerrePositivity.HomologicalAlgebra.DerivedQuotientBaseChange

/-!
# 有界 prism 上の完全平坦な対象の離散性

## 概要
完備で完全平坦な上に有界な導来対象は離散であり、その零次ホモロジーは古典的に完備。

## 方針
生成元の冪による導来剰余を通常の加群の剰余と同定し、正則性と有界ねじれを使う。

## 規約
BS 著者版 Lemma 3.7 (2) の上に有界な導来対象の場合。

## 使われ方
導来完備なテンソル積の離散性。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open CategoryTheory CategoryTheory.Limits DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

/-- 概要：完全平坦な導来完備対象は離散で、H⁰ は古典的に完備。生成元が H⁰ 上正則で各生成元冪剰余の p 冪ねじれが有界。
方針：生成元剰余による離散性の判定と、剰余の主元完備性を合わせる。
規約：BS 著者版 Lemma 3.7 (2) の上に有界な対象。
使われ方：完全平坦な完備底変換。 -/
theorem derivedCompletelyFlat_isDiscrete_of_boundedPrism
    {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
    (P : OrientedPrism p A) (hP : IsBoundedPrism P)
    (X : DerivedCategory.Minus (ModuleCat.{u} A))
    (hp : IsComplete A (p : A) X.obj) (hd : IsComplete A P.generator X.obj)
    (hf : IsDerivedCompletelyFlat (Ideal.span {(p : A), P.generator}) X) :
    let H := (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj X.obj
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧ IsAdicComplete (Ideal.span {(p : A), P.generator}) H ∧
      (∀ n : ℕ, IsSMulRegular H (P.generator ^ n)) ∧
      ∀ n : ℕ, ∃ N : ℕ, ∀ (k : ℕ) (x : H ⧸ (Ideal.span {P.generator ^ n} • ⊤ : Submodule A H)),
        (p : A) ^ k • x = 0 → (p : A) ^ N • x = 0 := by
  let d := P.generator
  let H := (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj X.obj
  have hPowers := derivedGeneratorPowerReduction_pure_bounded P hP X hp hf
  have hr₁ := hPowers 1
  have hregA : IsSMulRegular A d := P.generator_regular
  let d₁ := P.generator ^ (1 : ℕ)
  have hd₁ : d₁ = d := pow_one _
  have hPure := derived_pure_of_complete_regular_quotient_pure d₁ (hregA.pow 1) X
    (by rw [hd₁]; exact hd) (fun i hi ↦ by
    rcases lt_or_gt_of_ne hi with hi | hi
    · let := hr₁.1
      exact DerivedCategory.isZero_of_isGE _ 0 i hi
    · let := hr₁.2.1
      exact DerivedCategory.isZero_of_isLE _ 0 i hi)
  let := hPure.1
  let := hPure.2.1
  have hreg : IsSMulRegular H d := hd₁ ▸ hPure.2.2
  let e : X.obj ≅ (DerivedCategory.singleFunctor (ModuleCat A) 0).obj H :=
    normalizedPureHomologyIso X.obj 0
  let eb : X ≅ boundedAboveDerivedSingleFunctor.obj H := ObjectProperty.isoMk _ e
  let : IsAdicComplete (Ideal.span {d}) H :=
    (isModuleComplete_iff_isAdicComplete_of_regular A d H hreg).mp (isComplete_of_iso A d e hd)
  have hquot (n : ℕ) :
      let U := H ⧸ (Ideal.span {d ^ n} • ⊤ : Submodule A H)
      IsAdicComplete (Ideal.span {(p : A)}) U ∧
        ∃ N : ℕ, ∀ (k : ℕ) (x : U), (p : A) ^ k • x = 0 → (p : A) ^ N • x = 0 := by
    let I := Ideal.span {d ^ n}
    let Q := A ⧸ I
    let q := Ideal.Quotient.mk I
    let U := (quotientModuleFunctor I).obj H
    let Y := (boundedAboveDerivedBaseChange q).obj X
    let ey := DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso eb ≪≫
      derivedQuotientModuleIso I H (scalarExtensionTorVanishing_principal_pow_of_regular d
        hregA H hreg n))
    let eh := ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso ey ≪≫
      (realizedSingleH0Iso Q).app U).toLinearEquiv
    have hcomp : IsModuleComplete Q (q (p : A)) U :=
      isComplete_of_iso Q (q (p : A)) ey
        (derivedBaseChange_principal_isComplete A (p : A) (d ^ n) (hregA.pow n) X hp)
    obtain ⟨N, hN⟩ := (hPowers n).2.2
    have hbound : ∀ (k : ℕ) (x : U),
        (q (p : A)) ^ k • x = 0 → (q (p : A)) ^ N • x = 0 := by
      intro k x hx
      apply eh.symm.injective
      rw [map_smul, map_zero]
      apply hN k
      rw [← eh.symm.map_smul, hx, map_zero]
    have hc := isAdicComplete_of_isModuleComplete_of_bounded_torsion Q (q (p : A))
      U hcomp ⟨N, hbound⟩
    change IsAdicComplete (Ideal.span {(p : A)}) (AdicReduction I H) ∧ _
    have hm : (Ideal.span {(p : A)}).map (algebraMap A Q) = Ideal.span {q (p : A)} := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    rw [← hm] at hc
    refine ⟨(IsAdicComplete.map_algebraMap_iff (S := Q) (Ideal.span {(p : A)})
      (AdicReduction I H)).mp hc, ⟨N, fun k x hx ↦ ?_⟩⟩
    have hb := hbound k x
    rw [← map_pow, ← map_pow] at hb
    exact hb hx
  refine ⟨hPure.1, hPure.2.1, ?_, fun n ↦ hreg.pow n, fun n ↦ (hquot n).2⟩
  have hQ (n : ℕ) : IsAdicComplete (Ideal.span {(p : A)})
      (H ⧸ ((Ideal.span {d}) ^ n • ⊤ : Submodule A H)) := by
    rw [Ideal.span_singleton_pow]
    exact (hquot n).1
  let := hQ
  rw [← Set.singleton_union, Ideal.span_union, sup_comm]
  exact isAdicComplete_module_sup_of_complete_quotients (Ideal.span {d}) (Ideal.span {(p : A)})

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 3.7" (partial := special) "(1) と (2)（完全平坦な複体の離散性、通常の導来圏で、BS-W15 K4）、(3)（完全平坦な δ 代数から有界 prism、exists_boundedPrism_of_completelyFlat_deltaAlgebra）は本体。(4) は不要（D19）。向き付きの基底 ／ 11-11 更新（2） ／ 11-12 夜更新（ノート本文の更新時）"] _root_.SerrePositivity.BhattScholze.Prismatic.derivedCompletelyFlat_isDiscrete_of_boundedPrism
