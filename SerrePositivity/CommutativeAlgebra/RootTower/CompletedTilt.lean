module

public import SerrePositivity.CommutativeAlgebra.RootTower.CompletedRoots
public import SerrePositivity.CommutativeAlgebra.RootTower.CompletionFlat
public import SerrePositivity.CommutativeAlgebra.CompatibleRootsPerfectoid
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # 完備した根の塔のtilt核とperfectoid性の残りの条件

実際の根の座標からtiltを構成し、基底環のp正則性を完備塔へ移す。
最初のmod p Frobenius核の計算を条件として明示し、そこからFontaine核を導く。
この条件自体の具体的な証明はまだ必要である。
-/

@[expose] public noncomputable section
namespace SerrePositivity.Section2
variable (A : Type*) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : CompletedTower A t p))]

omit [Fact (¬ IsUnit (p : CompletedTower A t p))] in
/-- 完備塔は自身のpで生成されるイデアルについて完備。 -/
instance completedTower_isAdicComplete_span_p :
    IsAdicComplete (Ideal.span {(p : CompletedTower A t p)}) (CompletedTower A t p) := by
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using
    (IsAdicComplete.map_algebraMap_iff (Ideal.span {(p : Tower A t p)})
      (CompletedTower A t p)).mpr (AdicCompletion.isAdicComplete (Submodule.fg_span_singleton _))

/-- 根の座標をmod pへ移した、完備塔の実際のtiltの元。 -/
def completedTowerRootTilt (i : Fin h) : PreTilt (CompletedTower A t p) p :=
  compatibleRootsTilt (CompletedTower A t p) p (fun n ↦ completedTowerRoot A t p n i)
    (fun n ↦ completedTowerRoot_succ_pow A t p n i)

/-- このtiltの元のuntiltは、基底環の対応する座標の像。 -/
theorem completedTowerRootTilt_untilt (i : Fin h) :
    (completedTowerRootTilt A t p i).untilt = algebraMap A (CompletedTower A t p) (t i) := by
  rw [completedTowerRootTilt, compatibleRootsTilt_untilt, completedTowerRoot_zero]

/-- 最初のmod p Frobenius核を計算できれば、完備塔のtilt射影の核が決まる。 -/
theorem completedTowerRootTilt_coeff_zero_kernel
    (hp : IsSMulRegular A (p : A)) (i : Fin h) (hti : t i = (p : A))
    (hF : Function.Surjective (frobenius (ModP (CompletedTower A t p) p) p))
    (hker : ∀ z : ModP (CompletedTower A t p) p, z ^ p = 0 ↔ z ∈
      Ideal.span {(Ideal.Quotient.mk (Ideal.span {(p : CompletedTower A t p)})
        (completedTowerRoot A t p 1 i))}) :
    RingHom.ker (PreTilt.coeff 0 : PreTilt (CompletedTower A t p) p →+*
      ModP (CompletedTower A t p) p) = Ideal.span {completedTowerRootTilt A t p i} := by
  apply compatibleRootsTilt_coeff_zero_kernel (CompletedTower A t p) p
    (isSMulRegular_p_completedTower A t p hp) hF
    (fun n ↦ completedTowerRoot A t p n i) _
    (fun n ↦ completedTowerRoot_succ_pow A t p n i) hker
  simp only [completedTowerRoot_zero, hti, map_natCast]

/-- 完備塔のperfectoid性を、最初のmod p Frobenius核の計算へ帰着する。
基底環のp正則性と塔の実際の両立する根を使用し、perfectoid性の引用は使わない。 -/
theorem completedTower_isIntegralPerfectoid_of_frobenius_kernel
    (hp : IsSMulRegular A (p : A)) (i : Fin h) (hti : t i = (p : A))
    (hF : Function.Surjective (frobenius (ModP (CompletedTower A t p) p) p))
    (hker : ∀ z : ModP (CompletedTower A t p) p, z ^ p = 0 ↔ z ∈
      Ideal.span {(Ideal.Quotient.mk (Ideal.span {(p : CompletedTower A t p)})
        (completedTowerRoot A t p 1 i))}) : IsIntegralPerfectoid (CompletedTower A t p) p := by
  apply isIntegralPerfectoid_of_compatible_p_roots (CompletedTower A t p) p
    (isSMulRegular_p_completedTower A t p hp) hF
    (fun n ↦ completedTowerRoot A t p n i) _
    (fun n ↦ completedTowerRoot_succ_pow A t p n i) hker
  simp only [completedTowerRoot_zero, hti, map_natCast]

end SerrePositivity.Section2
