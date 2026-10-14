module

public import Mathlib.RingTheory.MvPowerSeries.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.WittVector.Complete

/-! # 冪級数環の係数の商とWitt係数のmod p比較

有限生成な核を持つ係数全射は、冪級数環でも全射であり、核は係数の核の拡大である。
その実際の商同型をWittの定数係数写像へ適用する。
根の塔や正規化長さはこの共通の係数比較には含めない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity

/-- 係数全射は、冪級数環の係数ごとの写像でも全射となる。 -/
theorem powerSeries_map_surjective {R S : Type u} [CommRing R] [CommRing S]
    (σ : Type v) (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (MvPowerSeries.map (σ := σ) f) := by
  intro φ
  choose a ha using fun d : σ →₀ ℕ ↦ hf (MvPowerSeries.coeff d φ)
  refine ⟨a, ?_⟩
  ext d
  exact ha d

/-- 係数写像の核が有限生成なら、係数の核の拡大で割った冪級数環は終域の冪級数環。 -/
def powerSeriesCoefficientQuotientEquiv {R S : Type u} [CommRing R] [CommRing S]
    (σ : Type v) (f : R →+* S) (hf : Function.Surjective f) (hker : (RingHom.ker f).FG) :
    MvPowerSeries σ R ⧸ (RingHom.ker f).map MvPowerSeries.C ≃+* MvPowerSeries σ S :=
  (Ideal.quotEquivOfEq (MvPowerSeries.ker_map_of_fg f hker).symm).trans
    (RingHom.quotientKerEquivOfSurjective (powerSeries_map_surjective σ f hf))

@[simp] theorem powerSeriesCoefficientQuotientEquiv_mk
    {R S : Type u} [CommRing R] [CommRing S] (σ : Type v) (f : R →+* S)
    (hf : Function.Surjective f) (hker : (RingHom.ker f).FG) (φ : MvPowerSeries σ R) :
    powerSeriesCoefficientQuotientEquiv σ f hf hker (Ideal.Quotient.mk _ φ) =
      MvPowerSeries.map f φ := rfl

/-- 完全標数p係数のWitt冪級数環をpで割ると、元の係数の冪級数環となる。 -/
def wittPowerSeriesModPEquiv (σ : Type v) (k : Type u) [CommRing k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] :
    MvPowerSeries σ (WittVector p k) ⧸ Ideal.span {(p : MvPowerSeries σ (WittVector p k))}
      ≃+* MvPowerSeries σ k := by
  have hker : (RingHom.ker (WittVector.constantCoeff : WittVector p k →+* k)).FG := by
    rw [WittVector.ker_constantCoeff]
    exact Submodule.fg_span_singleton _
  have heq : (RingHom.ker (WittVector.constantCoeff : WittVector p k →+* k)).map
      (MvPowerSeries.C (σ := σ)) = Ideal.span {(p : MvPowerSeries σ (WittVector p k))} := by
    rw [WittVector.ker_constantCoeff, Ideal.map_span, Set.image_singleton, map_natCast]
  exact (Ideal.quotEquivOfEq heq.symm).trans
    (powerSeriesCoefficientQuotientEquiv σ WittVector.constantCoeff
      (WittVector.constantCoeff_surjective p) hker)

/-- Witt係数のmod p同型は、代表元の各係数を定数係数へ送る。 -/
@[simp] theorem wittPowerSeriesModPEquiv_mk (σ : Type v) (k : Type u) [CommRing k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (φ : MvPowerSeries σ (WittVector p k)) :
    wittPowerSeriesModPEquiv σ k p (Ideal.Quotient.mk _ φ) =
      MvPowerSeries.map WittVector.constantCoeff φ := rfl

/-- Witt冪級数の表示を持つ環のmod p商と、剰余係数の冪級数環の同型。 -/
def wittPresentedModPEquiv (A : Type (max u v)) [CommRing A] (σ : Type v)
    (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (e : A ≃+* MvPowerSeries σ (WittVector p k)) :
    A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k :=
  (Ideal.quotientEquiv (Ideal.span {(p : A)})
    (Ideal.span {(p : MvPowerSeries σ (WittVector p k))}) e (by
      rw [Ideal.map_span, Set.image_singleton, map_natCast])).trans
    (wittPowerSeriesModPEquiv σ k p)

@[simp] theorem wittPresentedModPEquiv_mk (A : Type (max u v)) [CommRing A] (σ : Type v)
    (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (e : A ≃+* MvPowerSeries σ (WittVector p k)) (a : A) :
    wittPresentedModPEquiv A σ k p e (Ideal.Quotient.mk _ a) =
      MvPowerSeries.map WittVector.constantCoeff (e a) := rfl

/-- 表示の座標はmod pの同型でも同じ変数へ送られる。 -/
theorem wittPresentedModPEquiv_coordinate (A : Type (max u v)) [CommRing A] (σ : Type v)
    (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (e : A ≃+* MvPowerSeries σ (WittVector p k)) (a : A) (i : σ)
    (ha : e a = MvPowerSeries.X i) :
    wittPresentedModPEquiv A σ k p e (Ideal.Quotient.mk _ a) = MvPowerSeries.X i := by
  rw [wittPresentedModPEquiv_mk, ha, MvPowerSeries.map_X]

end SerrePositivity
