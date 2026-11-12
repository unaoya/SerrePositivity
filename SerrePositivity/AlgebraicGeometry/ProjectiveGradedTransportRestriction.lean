module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedTransportValues
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedDirectSumRestriction
public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizationMapRestriction

/-!
概要：加群の同値を経由する斉次局所化の直和比較を、標準開の制限と可換にする。
方針：周囲の局所化の比較と直和の比較に戻して、二つの自然性を合成する。
規約：分子の指定部分の対応を、両方の標準開について与える。
使われ方：Rees 加群の局所化の比較を、Čech 係数図式の比較にまとめる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped DirectSum
attribute [local instance] LocalizedModule.moduleOfIsLocalization

variable {R S κ : Type*} [CommRing R] [CommRing S] [Algebra R S] [DecidableEq κ]
variable {F : κ → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
variable [∀ i, Module S (F i)] [∀ i, IsScalarTower R S (F i)]
variable {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- 各成分の分子が追加因子で移るなら、同値で対応する加群の分子も移る。 -/
theorem projectiveGradedTransport_restriction_mem (a : S)
    (V W : ∀ i, ℕ → Submodule R (F i)) (U₀ U₁ : ℕ → Submodule R N)
    (e : (⨁ i, F i) ≃ₗ[S] N)
    (heV : ∀ k x, e x ∈ U₀ k ↔ x ∈ projectiveDirectSumSubmodule (fun i ↦ V i k))
    (heW : ∀ k x, e x ∈ U₁ k ↔ x ∈ projectiveDirectSumSubmodule (fun i ↦ W i k))
    (h : ∀ (i : κ) (k : ℕ) (m : V i k), a ^ k • m.val ∈ W i k)
    (k : ℕ) (m : U₀ k) : a ^ k • m.val ∈ U₁ k := by
  have hm : e.symm m.val ∈ projectiveDirectSumSubmodule (fun i ↦ V i k) :=
    (heV k (e.symm m.val)).mp (by simpa only [e.apply_symm_apply] using m.property)
  have hx := projectiveDirectSumSubmodule_restriction_mem a V W h k ⟨e.symm m.val, hm⟩
  have hy := (heW k (a ^ k • e.symm m.val)).mpr hx
  simpa only [map_smul, e.apply_symm_apply] using hy

/-- 斉次局所化の直和への移送は、標準開を狭める制限と可換。 -/
theorem projectiveGradedLocalizedDirectSumTransport_restriction
    {f g a : S} (ha : g = f * a)
    (V W : ∀ i, ℕ → Submodule R (F i)) (U₀ U₁ : ℕ → Submodule R N)
    (e : (⨁ i, F i) ≃ₗ[S] N)
    (heV : ∀ k x, e x ∈ U₀ k ↔ x ∈ projectiveDirectSumSubmodule (fun i ↦ V i k))
    (heW : ∀ k x, e x ∈ U₁ k ↔ x ∈ projectiveDirectSumSubmodule (fun i ↦ W i k))
    (hV : ∀ (i : κ) (k : ℕ) (m : V i k), f • m.val ∈ V i (k + 1))
    (hW : ∀ (i : κ) (k : ℕ) (m : W i k), g • m.val ∈ W i (k + 1))
    (h : ∀ (i : κ) (k : ℕ) (m : V i k), a ^ k • m.val ∈ W i k)
    (hU : ∀ k (m : U₀ k), a ^ k • m.val ∈ U₁ k)
    (z : projectiveGradedAway f U₀) :
    DirectSum.lmap (fun i ↦ projectiveGradedAwayRestriction ha (V i) (W i) (h i))
        (projectiveGradedLocalizedDirectSumTransport f V U₀ e heV hV z) =
      projectiveGradedLocalizedDirectSumTransport g W U₁ e heW hW
        (projectiveGradedAwayRestriction ha U₀ U₁ hU z) := by
  apply (DirectSum.lmap_injective
    (fun i ↦ (projectiveGradedAway g (W i)).subtype)).mpr (fun i ↦ Subtype.val_injective)
  apply DFinsupp.ext
  intro i
  change (projectiveGradedAwayRestriction ha (V i) (W i) (h i)
    ((projectiveGradedLocalizedDirectSumTransport f V U₀ e heV hV z) i)).val =
      ((projectiveGradedLocalizedDirectSumTransport g W U₁ e heW hW
        (projectiveGradedAwayRestriction ha U₀ U₁ hU z)) i).val
  rw [projectiveGradedAwayRestriction_val,
    projectiveGradedLocalizedDirectSumTransport_component_val,
    projectiveGradedLocalizedDirectSumTransport_component_val,
    projectiveGradedAwayRestriction_val]
  have heLoc := DFunLike.congr_fun (projectiveLocalizedModuleCongr_restriction
    (show f ∣ g from ⟨a, ha⟩) e.symm) z.val
  change projectiveLocalizedModuleCongr (Submonoid.powers g) e.symm
      (projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩) z.val) =
    projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩)
      (projectiveLocalizedModuleCongr (Submonoid.powers f) e.symm z.val) at heLoc
  rw [heLoc]
  exact (congrArg (fun x ↦ x i) (DFunLike.congr_fun
    (projectiveLocalizedDirectSumLinearEquiv_restriction (M := F)
      (show f ∣ g from ⟨a, ha⟩))
    (projectiveLocalizedModuleCongr (Submonoid.powers f) e.symm z.val))).symm

end SerrePositivity.AlgebraicGeometry
