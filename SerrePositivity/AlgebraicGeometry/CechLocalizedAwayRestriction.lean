module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedRestriction
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Tactic.Ring

/-!
概要：追加因子を外側で局所化すると、標準開の制限は同型になる。
方針：二重の分数を使い、全射性では追加因子を外側の分母へ移す。
規約：内側・外側の分母に非零因子性は仮定しない。
使われ方：アフィン標準被覆を各被覆元で局所化した後の、固定頂点による縮約。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] (S : Submonoid R)
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {f g a : R}

/-- 標準開の制限を、さらに外側の分母で局所化した写像。 -/
def cechLocalizedAwayRestriction (h : f ∣ g) :
    LocalizedModule S (LocalizedModule (Submonoid.powers f) M) →ₗ[R]
      LocalizedModule S (LocalizedModule (Submonoid.powers g) M) :=
  IsLocalizedModule.map S (LocalizedModule.mkLinearMap S _)
    (LocalizedModule.mkLinearMap S _) (projectiveModuleAwayRestriction h)

/-- 追加因子が外側で逆になるなら、局所化した制限は全射。 -/
theorem cechLocalizedAwayRestriction_surjective (hg : g = f * a) (ha : a ∈ S) :
    Function.Surjective (cechLocalizedAwayRestriction (M := M) S (show f ∣ g from ⟨a, hg⟩)) := by
  intro z
  induction z using LocalizedModule.induction_on with
  | _ x t =>
    induction x using LocalizedModule.induction_on with
    | _ m s =>
      obtain ⟨s, n, rfl⟩ := s
      let an : S := ⟨a ^ n, S.pow_mem ha n⟩
      refine ⟨LocalizedModule.mk (LocalizedModule.mk m (projDenominator f n)) (t * an), ?_⟩
      change IsLocalizedModule.map S (LocalizedModule.mkLinearMap S _)
        (LocalizedModule.mkLinearMap S _) (projectiveModuleAwayRestriction (show f ∣ g from ⟨a, hg⟩))
          (LocalizedModule.mk (LocalizedModule.mk m (projDenominator f n)) (t * an)) =
        LocalizedModule.mk (LocalizedModule.mk m (projDenominator g n)) t
      rw [IsLocalizedModule.map_LocalizedModules, projectiveModuleAwayRestriction_mk hg,
        ← LocalizedModule.smul'_mk]
      simpa only [an, Submonoid.smul_def] using
        (LocalizedModule.mk_cancel_common_right t an (LocalizedModule.mk m (projDenominator g n)))

/-- 追加因子が外側で逆になるなら、局所化した制限は単射。 -/
theorem cechLocalizedAwayRestriction_injective (hg : g = f * a) (ha : a ∈ S) :
    Function.Injective (cechLocalizedAwayRestriction (M := M) S (show f ∣ g from ⟨a, hg⟩)) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  change cechLocalizedAwayRestriction (M := M) S (show f ∣ g from ⟨a, hg⟩) z = 0 at hz
  revert hz
  induction z using LocalizedModule.induction_on with
  | _ x t =>
    induction x using LocalizedModule.induction_on with
    | _ m s =>
      intro hz
      obtain ⟨s, n, rfl⟩ := s
      change IsLocalizedModule.map S (LocalizedModule.mkLinearMap S _)
        (LocalizedModule.mkLinearMap S _) (projectiveModuleAwayRestriction (show f ∣ g from ⟨a, hg⟩))
          (LocalizedModule.mk (LocalizedModule.mk m (projDenominator f n)) t) = 0 at hz
      rw [IsLocalizedModule.map_LocalizedModules, projectiveModuleAwayRestriction_mk hg] at hz
      obtain ⟨b, hb⟩ := LocalizedModule.mk_eq.mp
        (hz.trans (LocalizedModule.zero_mk (1 : S)).symm)
      have hb' : (b : R) • LocalizedModule.mk (a ^ n • m) (projDenominator g n) = 0 := by
        simpa only [Submonoid.smul_def, one_smul, smul_zero] using hb
      rw [LocalizedModule.smul'_mk] at hb'
      obtain ⟨c, hc⟩ := LocalizedModule.mk_eq.mp
        (hb'.trans (LocalizedModule.zero_mk (1 : Submonoid.powers g)).symm)
      have hc' : (c : R) • ((b : R) • (a ^ n • m)) = 0 := by
        simpa only [Submonoid.smul_def, one_smul, smul_zero] using hc
      obtain ⟨c, k, rfl⟩ := c
      let v : S := b * ⟨a ^ (n + k), S.pow_mem ha (n + k)⟩
      rw [← LocalizedModule.zero_mk (1 : S)]
      apply LocalizedModule.mk_eq.mpr
      refine ⟨v, ?_⟩
      simp only [Submonoid.smul_def, one_smul, smul_zero]
      rw [LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk (1 : Submonoid.powers f)]
      apply LocalizedModule.mk_eq.mpr
      refine ⟨projDenominator f k, ?_⟩
      simp only [Submonoid.smul_def, one_smul, smul_zero, projDenominator]
      have hs : f ^ k * ((b : R) * a ^ (n + k)) = g ^ k * ((b : R) * a ^ n) := by
        rw [hg, mul_pow, pow_add]
        ring
      change f ^ k • (((b : R) * a ^ (n + k)) • m) = 0
      rw [← mul_smul, hs, mul_smul, mul_smul]
      exact hc'

/-- 追加因子を外側で逆にした標準開の制限は、実際の加群の同型。 -/
theorem cechLocalizedAwayRestriction_isIso (hg : g = f * a) (ha : a ∈ S) :
    IsIso (ModuleCat.ofHom (cechLocalizedAwayRestriction (M := M) S (show f ∣ g from ⟨a, hg⟩))) := by
  exact (LinearEquiv.ofBijective
    (cechLocalizedAwayRestriction (M := M) S (show f ∣ g from ⟨a, hg⟩))
      ⟨cechLocalizedAwayRestriction_injective S hg ha,
        cechLocalizedAwayRestriction_surjective S hg ha⟩).toModuleIso.isIso_hom

end SerrePositivity.AlgebraicGeometry
