module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.PrincipalRegularLift

/-!
概要：KST §5 の正則単項中心に対する中心外の検出射。
方針：像中心に属する b を可逆化すると、基底の中心の外に入る。
規約：局所射の一致には正則性による零核を別途使う。
使われ方：任意のアフィン開被覆による blowup の普遍写像の貼り合わせ。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {R S : Type u} [CommRing R] [CommRing S]
  (I : Ideal R) (f : R →+* S) (b : S)

set_option backward.isDefEq.respectTransparency false in
/--
概要：像中心の元 b を可逆化した Spec の像は基底の中心の補集合に入る。
方針：逆像素イデアルが中心を含めば、局所化で単元となる b を含む矛盾を得る。
規約：KST §5、ここでは b の正則性を要求しない。
使われ方：正則な b の局所化を零核の中心外検出射として使う。
-/
theorem principalDetector_range_complement (hb : b ∈ I.map f) :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away b))) ≫
      Spec.map (CommRingCat.ofHom f)) ⊆ (affineCenterComplement I).carrier := by
  rw [← Spec.map_comp]
  rintro _ ⟨x, rfl⟩
  apply (mem_affineCenterComplement I _).mpr
  intro hzero
  have hle : I ≤ Ideal.comap ((algebraMap S (Localization.Away b)).comp f) x.asIdeal :=
    fun r hr => hzero hr
  have hle' : I.map f ≤ Ideal.comap (algebraMap S (Localization.Away b)) x.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr hle
  exact Ideal.notMem_of_isUnit x.asIdeal (IsLocalization.Away.algebraMap_isUnit b) (hle' hb)

set_option backward.isDefEq.respectTransparency false in
/--
概要：正則な単項像中心を持つ局所射は任意の開集合との重なりで一意。
方針：正則生成元 b の局所化を零核の中心外検出射として使う。
規約：KST §5、b を中心元の像として選ぶ必要はない。
使われ方：任意のアフィン被覆上の普遍写像の貼り合わせ。
-/
theorem affineBlowup_principal_regular_overlap {T Z : Scheme.{u}}
    (hreg : b ∈ nonZeroDivisors S) (hI : I.map f = Ideal.span {b})
    (j : Spec (.of S) ⟶ T) (k : Z ⟶ T) [IsOpenImmersion k]
    (g : Spec (.of S) ⟶ affineBlowup I) (h : Z ⟶ affineBlowup I)
    (hg : g ≫ affineBlowupπ I = Spec.map (CommRingCat.ofHom f))
    (hbase : (pullback.fst j k ≫ g) ≫ affineBlowupπ I =
      (pullback.snd j k ≫ h) ≫ affineBlowupπ I) :
    pullback.fst j k ≫ g = pullback.snd j k ≫ h := by
  have := affineBlowupπ_restrict_complement_isIso I
  apply local_lift_overlap_hom_ext (affineBlowupπ I) (affineCenterComplement I)
    j k g h hbase (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away b))))
    (specMap_ker_eq_bot_of_injective _ (IsLocalization.injective
      (Localization.Away b) (Submonoid.powers_le.mpr hreg)))
  rw [hg]
  exact principalDetector_range_complement I f b
    (hI.symm ▸ Ideal.subset_span (Set.mem_singleton b))

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
