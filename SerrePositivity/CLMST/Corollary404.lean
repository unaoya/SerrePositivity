module

public import SerrePositivity.CLMST.KLFiniteComparisonExcision
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Corollary 4.0.4 の実証明

## 概要
原典入力と同じ署名で、局所コホモロジーと全有限段の Koszul ホモロジーの消滅を得る。

## 方針
有限比較 excision を実供給し、元の塔側の全冪ねじれ Tor 入力を KL-Q に渡す。
A への平坦底変換と全加群版への移送は既存の合流定理を使用する。
-/

set_option linter.unusedVariables false

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open IsLocalRing Section2

/--
## 概要
Cor 4.0.4 の原典署名の両消滅を、BS の二つの入力から証明する。

## 方針
perfectoid な絶対整閉拡大上の有限比較 excision を供給して、全冪ねじれ試験を得る。
全加群版と KL-Q の既存の合流で、元の ideal の全元による両消滅へ戻す。

## 規約
原典署名の全仮定を保持し、g の選択とパラメータ系の量化を変更しない。

## 使われ方
Inputs.corollary_4_0_4 の同じ署名の証明として用いる。
-/
theorem corollary_4_0_4
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharZero D] (htp : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)))
    (he : ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g))) :
    (∀ i : ℕ, i < h → ∀ a ∈ perfectoidIdeal (CompletedTower A t p) p hperf
      (algebraMap A (CompletedTower A t p) g),
      HomologicalAlgebra.localCohomologyScalarEndomorphism (maximalIdeal D) i
        (RPerfd A D t p hperf) (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf) a) = 0) ∧
    (∀ n : ℕ,
      let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ (y : Fin h → StageAlgebra A D t p n),
        IsSystemOfParameters (StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom
            (koszulHomologySelf (fun j ↦ toRPerfd A D t p hperf n (y j)) i)
            (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
          perfectoidIdeal (CompletedTower A t p) p hperf
            (algebraMap A (CompletedTower A t p) g) ≤
              Module.annihilator (CompletedTower A t p)
                (koszulHomologySelf (fun j ↦ toRPerfd A D t p hperf n (y j)) i)) := by
  exact rPerfd_cohomology_vanishing_of_finiteComparison_excision A t D p hperf
    ht hdimA hsop ⟨0, hpos⟩ htp g hEtale
    (fun E _ _ hE _ => klFiniteComparisonExcision_of_perfectoid E p hE)

end SerrePositivity.CLMST
