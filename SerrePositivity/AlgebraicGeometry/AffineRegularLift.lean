module

public import SerrePositivity.AlgebraicGeometry.ChartRegularLift
public import SerrePositivity.AlgebraicGeometry.ChartGluing
public import SerrePositivity.AlgebraicGeometry.LocalLiftGluing

/-!
概要：KST §5 の通常 blowup への正則な単項中心からの持ち上げ。
方針：標準チャートの環準同型に Spec を適用し、正則局所化と分離性で一意性を示す。
規約：中心の像の生成元は指定した a の像とする。
使われ方：blowup の普遍性と admissible な共通細分。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {R S : Type u} [CommRing R] [CommRing S]
  (I : Ideal R) (f : R →+* S) (a : I)

/--
概要：像中心が正則な f(a) で生成されるときの通常 blowup への実際の射。
方針：正則チャート持ち上げの Spec と標準チャートの開埋め込みを合成する。
規約：KST §5、通常の Rees blowup を標的とする。
使われ方：中心の逆像が正則な単項イデアルとなるアフィン開集合上の普遍写像。
-/
def affineBlowupRegularLift (hreg : f a.1 ∈ nonZeroDivisors S)
    (hI : I.map f = Ideal.span {f a.1}) : Spec (.of S) ⟶ affineBlowup I :=
  Spec.map (CommRingCat.ofHom (chartRegularLift I f a hreg hI)) ≫
    affineBlowupChartι I a

set_option backward.isDefEq.respectTransparency false in
/--
概要：正則な単項中心からの持ち上げは指定された基底射を持つ。
方針：標準チャートの構造射と持ち上げ環準同型の係数保存を使う。
規約：KST §5、両辺は Spec R へのスキーム射。
使われ方：局所的な持ち上げを基底上で貼り合わせる。
-/
@[reassoc] theorem affineBlowupRegularLift_base
    (hreg : f a.1 ∈ nonZeroDivisors S) (hI : I.map f = Ideal.span {f a.1}) :
    affineBlowupRegularLift I f a hreg hI ≫ affineBlowupπ I =
      Spec.map (CommRingCat.ofHom f) := by
  unfold affineBlowupRegularLift
  rw [Category.assoc, show affineBlowupChartι I a ≫ affineBlowupπ I =
    Spec.map (CommRingCat.ofHom (chartBaseMap I a)) from affineBlowupChartIso_inv_ι_π I a,
    ← Spec.map_comp]
  congr 1
  ext r
  exact chartRegularLift_base I f a hreg hI r

set_option backward.isDefEq.respectTransparency false in
/--
概要：正則な f(a) を持つアフィン基底からの通常 blowup への射は基底上で一意。
方針：f(a) の局所化は零核で、そこでは基底射の像が D(a) に入る。
規約：KST §5、中心の像の単項生成は一意性には不要。
使われ方：異なる生成元による局所的な普遍写像の一致。
-/
theorem affineBlowup_hom_ext_of_regular (hreg : f a.1 ∈ nonZeroDivisors S)
    {g h : Spec (.of S) ⟶ affineBlowup I}
    (hg : g ≫ affineBlowupπ I = Spec.map (CommRingCat.ofHom f))
    (hh : h ≫ affineBlowupπ I = Spec.map (CommRingCat.ofHom f)) : g = h := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f a.1))))
  apply hom_ext_of_ker_eq_bot_of_separated (affineBlowupπ I) (hg.trans hh.symm) j
    (specMap_ker_eq_bot_of_injective _ (IsLocalization.injective
      (Localization.Away (f a.1)) (Submonoid.powers_le.mpr hreg)))
  have : IsIso (affineBlowupπ I ∣_ PrimeSpectrum.basicOpen a.1) :=
    affineBlowupπ_restrict_basicOpen_isIso I a
  apply hom_ext_of_isIso_restrict (affineBlowupπ I) (PrimeSpectrum.basicOpen a.1)
  · simp only [Category.assoc, hg, hh]
  · rw [Category.assoc, hg]
    dsimp only [j]
    rw [← Spec.map_comp]
    rintro _ ⟨x, rfl⟩
    change algebraMap S (Localization.Away (f a.1)) (f a.1) ∉ x.asIdeal
    exact Ideal.notMem_of_isUnit _ (IsLocalization.Away.algebraMap_isUnit _)

set_option backward.isDefEq.respectTransparency false in
/--
概要：正則な像中心元を持つアフィン局所射は、任意の開集合との重なりで一意。
方針：正則像中心元を可逆化する検出射を重なりに引き戻す。
規約：KST §5、重なり自体がアフィンである必要はない。
使われ方：正則単項中心からの普遍写像の貼り合わせ。
-/
theorem affineBlowup_regular_overlap {T Z : Scheme.{u}}
    (hreg : f a.1 ∈ nonZeroDivisors S)
    (j : Spec (.of S) ⟶ T) (k : Z ⟶ T) [IsOpenImmersion k]
    (g : Spec (.of S) ⟶ affineBlowup I) (h : Z ⟶ affineBlowup I)
    (hg : g ≫ affineBlowupπ I = Spec.map (CommRingCat.ofHom f))
    (hbase : (Limits.pullback.fst j k ≫ g) ≫ affineBlowupπ I =
      (Limits.pullback.snd j k ≫ h) ≫ affineBlowupπ I) :
    Limits.pullback.fst j k ≫ g = Limits.pullback.snd j k ≫ h := by
  have := affineBlowupπ_restrict_basicOpen_isIso I a
  apply local_lift_overlap_hom_ext (affineBlowupπ I) (PrimeSpectrum.basicOpen a.1)
    j k g h hbase
    (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f a.1)))))
    (specMap_ker_eq_bot_of_injective _ (IsLocalization.injective
      (Localization.Away (f a.1)) (Submonoid.powers_le.mpr hreg)))
  rw [hg, ← Spec.map_comp]
  rintro _ ⟨x, rfl⟩
  change algebraMap S (Localization.Away (f a.1)) (f a.1) ∉ x.asIdeal
  exact Ideal.notMem_of_isUnit _ (IsLocalization.Away.algebraMap_isUnit _)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
