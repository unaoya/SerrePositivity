module

public import SerrePositivity.AlgebraicGeometry.ChartLocalization
public import SerrePositivity.AlgebraicGeometry.ProjBase
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
概要：KST §5 の blowup が中心の補開集合上で同型であることを示す。
方針：π⁻¹D(a) は a の標準チャートに入り、そこで環の局所化同型を使う。
規約：アフィン基底について中心の有限生成性を要求しない。
使われ方：抽象 blowup 正方形と Stacks 081T の admissible 条件。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry

open Polynomial _root_.AlgebraicGeometry CategoryTheory

variable {R : Type u} [CommRing R] (I : Ideal R)

/--
概要：アフィン blowup の構造射での D(r) の逆像。
方針：Rees の零次成分の同定と Proj の基本開集合の逆像公式を使う。
規約：KST §5、r は基礎環の任意の元。
使われ方：中心を避ける部分の点を斉次素イデアルで判定する。
-/
theorem affineBlowupπ_preimage_basicOpen (r : R) :
    affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen r =
      Proj.basicOpen (reesGrade I) (algebraMap R (reesAlgebra I) r) := by
  ext x
  change ¬ (reesZeroEquiv I).symm r ∈ (Proj.toSpecZero (reesGrade I) x).asIdeal ↔ _
  exact not_congr (proj_toSpecZero_mem (reesGrade I) x ((reesZeroEquiv I).symm r))

/--
概要：a ∈ I に対し、D(a) の逆像は a の標準 blowup チャートに含まれる。
方針：a t を含む斉次素イデアルが a を含まないと、次数一元を全て含み被覆性に反する。
規約：KST §5、基礎環内での a の非零因子性は不要。
使われ方：補開集合上の構造射を一つのアフィンチャートで計算する。
-/
theorem affineBlowupπ_preimage_basicOpen_le_chart (a : I) :
    affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen a.1 ≤ affineBlowupChart I a := by
  rw [affineBlowupπ_preimage_basicOpen]
  intro x hx
  change reesDegreeOne I a ∉ x.asHomogeneousIdeal
  intro ha
  have hcoeff : algebraMap R (reesAlgebra I) a.1 ∉ x.asHomogeneousIdeal := hx
  have hall (b : I) : reesDegreeOne I b ∈ x.asHomogeneousIdeal := by
    have heq : algebraMap R (reesAlgebra I) a.1 * reesDegreeOne I b =
        algebraMap R (reesAlgebra I) b.1 * reesDegreeOne I a := by
      apply Subtype.ext
      simp [reesDegreeOne, reesMonomial, mul_comm]
    have hmul : algebraMap R (reesAlgebra I) a.1 * reesDegreeOne I b ∈
        x.asHomogeneousIdeal.toIdeal := by
      rw [heq]
      exact x.asHomogeneousIdeal.toIdeal.mul_mem_left _ ha
    exact (x.isPrime.mul_mem_iff_mem_or_mem.mp hmul).resolve_left hcoeff
  have htop : x ∈ (⊤ : (affineBlowup I).Opens) := trivial
  rw [← iSup_affineBlowupChart I] at htop
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp htop
  exact hb (hall b)

/--
概要：係数写像の局所化は構成済みの補開集合上の環同型に一致する。
方針：局所化の準同型の一意性と基礎環の係数保存を使う。
規約：KST §5、両辺の始域は R[1/a]。
使われ方：Spec の基本開集合への制限で同型の instance を得る。
-/
lemma chartAwayEquiv_toRingHom (a : I) :
    (chartAwayEquiv I a).toRingHom = Localization.awayMap (chartBaseMap I a) a.1 := by
  apply IsLocalization.ringHom_ext (Submonoid.powers a.1)
  ext r
  simp [chartAwayEquiv_apply_base, chartAwayBaseMap, Localization.awayMap,
    IsLocalization.Away.map]

/--
概要：標準チャートの Spec から基礎環の Spec への射は D(a) 上で同型。
方針：Spec の基本開集合への制限を局所化準同型に移し、その環同型を適用する。
規約：KST §5、制限の始域も D(a) の逆像に制限する。
使われ方：blowup 全体の中心の外での同型。
-/
theorem chartSpecMap_restrict_isIso (a : I) :
    IsIso (Spec.map (CommRingCat.ofHom (chartBaseMap I a)) ∣_
      PrimeSpectrum.basicOpen a.1) := by
  have : IsIso (CommRingCat.ofHom (Localization.awayMap (chartBaseMap I a) a.1)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    rw [← chartAwayEquiv_toRingHom]
    exact (chartAwayEquiv I a).bijective
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (chartBaseMap I a)) a.1)).mpr
      (inferInstanceAs (IsIso (Spec.map
        (CommRingCat.ofHom (Localization.awayMap (chartBaseMap I a) a.1)))))

set_option backward.isDefEq.respectTransparency false in
/--
概要：開埋め込みの像が指定した逆像開集合を含めば、その開集合上の制限は同型。
方針：制限射は開埋め込みであり、像の仮定から全射になる。
規約：KST §5 の開チャート比較に用いる一般のスキーム射について述べる。
使われ方：中心を避ける部分の計算を標準チャートから blowup 全体へ移す。
-/
theorem isIso_restrict_openImmersion_of_le_range {X Y Z : Scheme}
    (g : X ⟶ Y) [IsOpenImmersion g] (f : Y ⟶ Z) (V : Z.Opens)
    (h : f ⁻¹ᵁ V ≤ g.opensRange) : IsIso (g ∣_ f ⁻¹ᵁ V) := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro y
  obtain ⟨x, hx⟩ := h y.2
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change g x ∈ f ⁻¹ᵁ V
    rw [hx]
    exact y.2
  · apply Subtype.ext
    rw [morphismRestrict_base_coe]
    exact hx

set_option backward.isDefEq.respectTransparency false in
/--
概要：a ∈ I に対し、アフィン blowup の構造射は D(a) 上で同型。
方針：D(a) の逆像を a の標準チャートに入れ、チャート環の局所化同型に帰着する。
規約：KST §5、有限生成性と Noether 性を要求しない。
使われ方：中心の補開集合全体での同型を局所判定する。
-/
theorem affineBlowupπ_restrict_basicOpen_isIso (a : I) :
    IsIso (affineBlowupπ I ∣_ PrimeSpectrum.basicOpen a.1) := by
  let g := Proj.awayι (reesGrade I) (reesDegreeOne I a) (reesDegreeOne_mem I a) (by decide)
  have hcomp : g ≫ affineBlowupπ I = Spec.map (CommRingCat.ofHom (chartBaseMap I a)) :=
    affineBlowupChartIso_inv_ι_π I a
  have : IsIso (g ∣_ affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen a.1) :=
    isIso_restrict_openImmersion_of_le_range g (affineBlowupπ I) _ (by
      rw [show g.opensRange = affineBlowupChart I a from Proj.opensRange_awayι ..]
      exact affineBlowupπ_preimage_basicOpen_le_chart I a)
  have h : IsIso ((g ≫ affineBlowupπ I) ∣_ PrimeSpectrum.basicOpen a.1) := by
    rw [hcomp]
    exact chartSpecMap_restrict_isIso I a
  rw [morphismRestrict_comp] at h
  exact IsIso.of_isIso_comp_left
    (g ∣_ affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen a.1)
    (affineBlowupπ I ∣_ PrimeSpectrum.basicOpen a.1)

/--
概要：アフィン中心 V(I) の補開集合。
方針：a ∈ I の基本開集合 D(a) の合併を取る。
規約：KST §5、中心の被約化を必要としない。
使われ方：blowup 構造射が同型になる基底の開集合。
-/
def affineCenterComplement : (Spec (.of R)).Opens :=
  ⨆ a : I, PrimeSpectrum.basicOpen a.1

/--
概要：定義した中心の補開集合の点は V(I) の外の点と一致する。
方針：I を含まない素イデアルから含まれない元を選ぶ。
規約：KST §5、V(I) は通常の素スペクトルの零点集合。
使われ方：D(I) による定義と X \ V(I) の表記を接続する。
-/
theorem mem_affineCenterComplement (x : PrimeSpectrum R) :
    x ∈ affineCenterComplement I ↔ x ∉ PrimeSpectrum.zeroLocus (I : Set R) := by
  classical
  constructor
  · intro hx hI
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ha (hI a.2)
  · intro h
    by_contra hnot
    apply h
    intro r hr
    by_contra hmem
    exact hnot (TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨r, hr⟩, hmem⟩)

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン blowup の構造射は中心の補開集合全体で同型。
方針：各 D(a) 上の同型を、同型性が標的の Zariski 局所的性質であることからまとめる。
規約：KST §5、中心と基礎環の有限生成性や Noether 性は不要。
使われ方：通常の blowup が中心の外で同型であるという幾何学的入力。
-/
theorem affineBlowupπ_restrict_complement_isIso :
    IsIso (affineBlowupπ I ∣_ affineCenterComplement I) := by
  let U := affineCenterComplement I
  let V (a : I) := U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen a.1
  have hV : iSup V = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨a, ha⟩
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) V hV
  intro a
  rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict (affineBlowupπ I) U (V a))]
  have heq : U.ι ''ᵁ V a = PrimeSpectrum.basicOpen a.1 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (le_iSup (fun a : I => PrimeSpectrum.basicOpen a.1) a)
  rw [heq]
  exact affineBlowupπ_restrict_basicOpen_isIso I a

/--
概要：アフィン blowup と基底の中心の補開集合との実際のスキーム同型。
方針：中心の補開集合への構造射の制限を同型として束ねる。
規約：KST §5、同型の順方向は構造射の制限である。
使われ方：抽象 blowup 正方形の補開集合上の同型を与える。
-/
def affineBlowupAwayIso :
    (affineBlowupπ I ⁻¹ᵁ affineCenterComplement I).toScheme ≅
      (affineCenterComplement I).toScheme := by
  letI := affineBlowupπ_restrict_complement_isIso I
  exact asIso (affineBlowupπ I ∣_ affineCenterComplement I)

/--
概要：中心の外での blowup 同型は元の構造射と両立する。
方針：スキーム射の開集合への制限の交換式を使う。
規約：KST §5、同型の順方向を blowup 構造射の制限とした規約。
使われ方：K-L5 の underlying scheme との比較と抽象 blowup 正方形。
-/
@[reassoc] theorem affineBlowupAwayIso_hom_ι :
    (affineBlowupAwayIso I).hom ≫ (affineCenterComplement I).ι =
      (affineBlowupπ I ⁻¹ᵁ affineCenterComplement I).ι ≫ affineBlowupπ I :=
  morphismRestrict_ι _ _

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
