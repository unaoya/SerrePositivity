module

public import SerrePositivity.CLMST.StageLocality
public import SerrePositivity.CLMST.EtaleLocus
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyAction
public import SerrePositivity.CommutativeAlgebra.Multiplicity
public import SerrePositivity.CommutativeAlgebra.Koszul
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-! # CLMST Corollary 4.0.4 の二つの消滅（文献入力）

固定した非零元 g に対し、局所コホモロジーの下次数の消滅と、
任意の有限段 A_n ⊗[A] D のパラメータ系の正次数 Koszul 消滅を引用する。
g を反転した有限エタール性を明示する。g の存在・選択はこの引用に含めない。

局所コホモロジーは D 上の Mathlib の Ext 余極限の定義を使い、
perfectoid ideal の各元による誘導乗法射が零と述べる。
Mathlib に未実装の局所コホモロジーの線形性を使って加群作用を仮定しない。
有限段の局所性は構成から証明し、その局所環構造の下で述べる。

出典：https://arxiv.org/html/2209.04046v4 （Notation 4.0.1, Corollary 4.0.4）。
-/

public section
universe u
namespace SerrePositivity.CLMST.Inputs
open IsLocalRing Section2

/-- CLMST Corollary 4.0.4：局所コホモロジーと全有限段の Koszul ホモロジーの almost 消滅。
原典の両成分を保持し、n=0 への特殊化や g の存在を引用の内部へ隠さない。 -/
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
  sorry

end SerrePositivity.CLMST.Inputs
