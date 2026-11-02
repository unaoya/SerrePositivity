module

public import SerrePositivity.CLMST.Corollary404
public import SerrePositivity.CLMST.StageLocality
public import SerrePositivity.CLMST.EtaleLocus
public import SerrePositivity.HomologicalAlgebra.LocalCohomology.Actions
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Basic
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# CLMST Corollary 4.0.4 の二つの消滅

## 概要
固定した g の外での有限エタール性から、低次局所コホモロジーと
全有限段の任意パラメータ系の正次数 Koszul ホモロジーの almost 消滅を得る。

## 方針
同じ署名の CLMST.corollary_4_0_4 により、有限比較 excision、全冪ねじれ Tor 入力、
平坦底変換、全加群版と KL-Q の実合流を使う。g の存在・選択は含めない。

## 使われ方
既存の Inputs 名と原典の全署名を保持する。局所コホモロジーには元の誘導乗法射を用いる。
原典：https://arxiv.org/html/2209.04046v4 （Notation 4.0.1, Corollary 4.0.4）。
-/

public section
universe u
namespace SerrePositivity.CLMST.Inputs
open IsLocalRing Section2

/--
## 概要
Cor 4.0.4 の局所コホモロジーと全有限段の Koszul ホモロジーの almost 消滅。

## 方針
同署名の実証明 CLMST.corollary_4_0_4 を適用する。

## 規約
原典の両成分を保持し、n=0 への特殊化や g の存在を内部へ隠さない。

## 使われ方
従来の文献入力名を保持して、既存の主定理への適用を実証明へ接続する。
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
  exact SerrePositivity.CLMST.corollary_4_0_4 A D hinj hres t hdimA hdimD
    hpos ht hsop p htp e he hperf g hg hEtale

end SerrePositivity.CLMST.Inputs
