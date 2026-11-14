module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Prism.Perfection.PrismPerfection
public import SerrePositivity.BhattScholze.Prismatic.Site.PrismOver
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion

/-!
# perfectoid 環の完全 prism による表示

## 概要
任意の整 perfectoid 環を、有界な完全 prism の生成元剰余として表示する。
## 方針
非零の枝では既存の Fontaine の核と完備 Witt prism を使う。
零環の枝では零環自身の prism を使う。
## 規約
BS 著者版 Theorem 3.10・Proposition 7.10。固定 A_inf との同一視をこの表示の定義にはしない。
## 使われ方
根付き基底 R′ の上で有限正則列の実包絡を構成する入口。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open DerivedCompletion Prismatic
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R]

/-- 零環上の prism。乗法の単射性と二つの完備性を直接示し、零環の剰余表示に使う。 -/
private def zeroPrism [Subsingleton R] : OrientedPrism p R := by
  let D := (DeltaStructure.existsUnique_of_mod_p
    (show Function.Injective (fun x : R => (p : R) * x) from fun _ _ _ => Subsingleton.elim _ _)
    (RingHom.id R) (fun _ => Subsingleton.elim _ _)).choose
  exact ⟨D, 0, fun _ _ _ => Subsingleton.elim _ _,
    isModuleComplete_of_pow_smul_zero R (p : R) (ModuleCat.of R R) 0
      (fun _ => Subsingleton.elim _ _),
    isModuleComplete_of_pow_smul_zero R 0 (ModuleCat.of R R) 0
      (fun _ => Subsingleton.elim _ _),
    by have hp0 : (p : R) = 0 := Subsingleton.elim _ _
       rw [hp0]
       exact Ideal.zero_mem _⟩

/-- 概要：整 perfectoid 環は有界な完全 prism の剰余として表示できる。
方針：既存の完備 Witt prism の剰余同型と、零環の直接の構成を合わせる。
規約：BS 著者版 Theorem 3.10・Proposition 7.10。非零性の追加仮定はない。
使われ方：有限 T の表示の基底 prism の供給。 -/
theorem exists_boundedPerfectPrismPresentation (hR : IsIntegralPerfectoid R p) :
    ∃ (A : CommRingCat.{u}) (P : OrientedPrism p A),
      P.deltaStructure.IsPerfect ∧ IsBoundedPrism P ∧ Nonempty (A ⧸ P.ideal ≃+* R) := by
  rcases hR with hs | ⟨hp, hc, ⟨π, u, hu⟩, hF, hk⟩
  · letI : Subsingleton R := hs
    let P := zeroPrism p R
    have hperf : P.deltaStructure.IsPerfect :=
      ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
    have hb : IsBoundedPrism P := ⟨0, fun _ _ _ => Subsingleton.elim _ _⟩
    letI : Unique R := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
    letI : Unique (R ⧸ P.ideal) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
    exact ⟨CommRingCat.of R, P, hperf, hb, ⟨RingEquiv.ofUnique⟩⟩
  · letI : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    letI := hc
    obtain ⟨d, hd, e, _⟩ := exists_perfectoidTrialPrism R p hF hk π u hu
    letI := pdCompletionCommRing (WittVector p (PreTilt R p)) p d
    let P := perfectDeltaPDPrism (wittDeltaStructure p (PreTilt R p))
      (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    have hperf : P.deltaStructure.IsPerfect := perfectDeltaPDPrism_isPerfect _ _ _ _
    have hb : IsBoundedPrism P := by
      refine ⟨1, fun n x hx => ?_⟩
      apply e.injective
      have hxe : (p : R)^n * e x = 0 := by
        simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg e hx
      have hpR : IsIntegralPerfectoid R p := Or.inr ⟨hp, hc, ⟨π,u,hu⟩,hF,hk⟩
      have h := hpR.p_mul_eq_zero_of_pow_mul_eq_zero R p n (e x) hxe
      simpa only [map_mul, map_pow, map_natCast, map_zero, pow_one] using h
    exact ⟨CommRingCat.of _, P, hperf, hb, ⟨e⟩⟩

end SerrePositivity.BhattScholze.Semiperfectoid
