module

public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedDirectSumComponents
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedLocalizationCongr
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedRestriction

/-!
概要：局所化の係数写像と、標準開を狭める制限写像との可換性。
方針：周囲の局所化の分数で計算し、指定次数の成分への制限にも同じ式を使う。
規約：係数写像は局所化する環の上で線形とする。
使われ方：Rees 加群の分子の比較と、Rees 次数を移す写像の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
attribute [local instance] LocalizedModule.moduleOfIsLocalization

section Ambient
variable {S M N : Type*} [CommRing S]
variable [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]

/-- 局所化した加群写像は、分母の整除から得られる制限と可換。 -/
theorem projectiveLocalizedModuleMap_restriction {f g : S} (h : f ∣ g) (u : M →ₗ[S] N) :
    (IsLocalizedModule.map (Submonoid.powers g)
        (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers g) N) u).comp
        (projectiveModuleAwayRestriction (M := M) h) =
      (projectiveModuleAwayRestriction (M := N) h).comp
        (IsLocalizedModule.map (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) N) u) := by
  obtain ⟨a, ha⟩ := h
  apply LinearMap.ext
  intro z
  induction z using LocalizedModule.induction_on with
  | _ m s =>
    obtain ⟨s, k, rfl⟩ := s
    change IsLocalizedModule.map (Submonoid.powers g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) N) u
      (projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩)
        (LocalizedModule.mk m (projDenominator f k))) =
      projectiveModuleAwayRestriction (M := N) (show f ∣ g from ⟨a, ha⟩)
        (IsLocalizedModule.map (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) N) u
          (LocalizedModule.mk m (projDenominator f k)))
    rw [projectiveModuleAwayRestriction_mk ha, IsLocalizedModule.map_LocalizedModules,
      IsLocalizedModule.map_LocalizedModules, projectiveModuleAwayRestriction_mk ha, map_smul]

/-- 加群同値を局所化する比較も、標準開の制限に自然。 -/
theorem projectiveLocalizedModuleCongr_restriction {f g : S} (h : f ∣ g) (e : M ≃ₗ[S] N) :
    (projectiveLocalizedModuleCongr (Submonoid.powers g) e).toLinearMap.comp
        (projectiveModuleAwayRestriction (M := M) h) =
      (projectiveModuleAwayRestriction (M := N) h).comp
        (projectiveLocalizedModuleCongr (Submonoid.powers f) e).toLinearMap :=
  projectiveLocalizedModuleMap_restriction h e.toLinearMap

end Ambient

section Graded
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- 指定次数の局所化の係数写像は、標準開の制限に自然。 -/
theorem projectiveGradedAwayMap_restriction {f g a : S} (ha : g = f * a)
    (V W : ℕ → Submodule R M) (V' W' : ℕ → Submodule R N)
    (u : M →ₗ[S] N) (huV : ∀ k x, x ∈ V k → u x ∈ V' k)
    (huW : ∀ k x, x ∈ W k → u x ∈ W' k)
    (hM : ∀ k (m : V k), a ^ k • m.val ∈ W k)
    (hN : ∀ k (m : V' k), a ^ k • m.val ∈ W' k)
    (z : projectiveGradedAway f V) :
    projectiveGradedAwayMap g W W' u huW (projectiveGradedAwayRestriction ha V W hM z) =
      projectiveGradedAwayRestriction ha V' W' hN (projectiveGradedAwayMap f V V' u huV z) := by
  apply Subtype.ext
  change IsLocalizedModule.map (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) N) u
    (projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩) z.val) =
      projectiveModuleAwayRestriction (M := N) (show f ∣ g from ⟨a, ha⟩)
        (IsLocalizedModule.map (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) N) u z.val)
  exact DFunLike.congr_fun (projectiveLocalizedModuleMap_restriction
    (show f ∣ g from ⟨a, ha⟩) u) z.val

/-- 分子を対応させる同値の斉次局所化も、標準開の制限に自然。 -/
theorem projectiveGradedAwayCongr_restriction {f g a : S} (ha : g = f * a)
    (e : M ≃ₗ[S] N) (V W : ℕ → Submodule R M) (V' W' : ℕ → Submodule R N)
    (heV : ∀ k x, e x ∈ V' k ↔ x ∈ V k)
    (heW : ∀ k x, e x ∈ W' k ↔ x ∈ W k)
    (hM : ∀ k (m : V k), a ^ k • m.val ∈ W k)
    (hN : ∀ k (m : V' k), a ^ k • m.val ∈ W' k)
    (z : projectiveGradedAway f V) :
    projectiveGradedAwayCongr g e W W' heW (projectiveGradedAwayRestriction ha V W hM z) =
      projectiveGradedAwayRestriction ha V' W' hN (projectiveGradedAwayCongr f e V V' heV z) :=
  projectiveGradedAwayMap_restriction ha V W V' W' e.toLinearMap
    (fun k x hx ↦ (heV k x).mpr hx) (fun k x hx ↦ (heW k x).mpr hx) hM hN z

end Graded
end SerrePositivity.AlgebraicGeometry
