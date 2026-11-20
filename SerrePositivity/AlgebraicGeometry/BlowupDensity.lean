module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.SchemeExceptional
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupAway

/-!
概要：Stacks 081T の最初の Cartier 化で得る blowup の中心外開集合の稠密性。
方針：各標準チャートで正則な係数を局所化した射が稠密であることを使う。
規約：ここでは位相的稠密性を述べ、スキーム論的稠密性とは区別する。
使われ方：固有な strict transform が開部分スキームになった後の全体との同定。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/--
概要：標準チャートの正則な係数を局所化した Spec の射は稠密。
方針：局所化準同型の単射性から核が零となり、素スペクトルの像の閉包公式を使う。
規約：KST §5、Stacks 081T の中心外の稠密性のアフィン計算。
使われ方：中心外開集合の各チャートでの稠密性。
-/
theorem chartLocalizationι_denseRange {R : Type u} [CommRing R] (I : Ideal R) (a : I) :
    DenseRange (chartLocalizationι I a) := by
  change DenseRange (PrimeSpectrum.comap
    (algebraMap (BlowupChartRing I a) (BlowupChartAway I a)))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  have hker : RingHom.ker (algebraMap (BlowupChartRing I a) (BlowupChartAway I a)) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp
      (IsLocalization.injective (BlowupChartAway I a)
        (Submonoid.powers_le.mpr (chartBaseMap_mem_nonZeroDivisors I a)))
  rw [hker]
  exact bot_le

variable {X : Scheme.{u}} (I : X.IdealSheafData)

set_option maxHeartbeats 800000 in
-- 一般スキームと切断環の Spec の逆像の依存型の同一視が標準制限を超えるため。
set_option backward.isDefEq.respectTransparency false in
/--
概要：標準チャートの正則な係数の局所化の像は中心外の逆像に入る。
方針：チャート上の D(a) をアフィン中心の補集合に含め、一般の補集合へ移す。
規約：Stacks 081T、中心の有限生成性は不要。
使われ方：チャートの稠密像を中心外開集合へ含める。
-/
theorem blowupChartLocalization_range (U : X.affineOpens) (a : I.ideal U) :
    Set.range (chartLocalizationι (I.ideal U) a ≫ blowupChartι I U a) ⊆
      (blowupπ I ⁻¹ᵁ centerComplement I).carrier := by
  rintro _ ⟨x, rfl⟩
  change (chartLocalizationι (I.ideal U) a ≫ blowupChartι I U a ≫ blowupπ I) x ∈
    centerComplement I
  rw [blowupChartι_π I U a]
  change (Spec.map (CommRingCat.ofHom (chartBaseMap (I.ideal U) a)))
    (chartLocalizationι (I.ideal U) a x) ∈ U.2.fromSpec ⁻¹ᵁ centerComplement I
  rw [fromSpec_preimage_centerComplement I U]
  have hs : affineBlowupChartι (I.ideal U) a ≫ affineBlowupπ (I.ideal U) =
      Spec.map (CommRingCat.ofHom (chartBaseMap (I.ideal U) a)) :=
    affineBlowupChartIso_inv_ι_π (I.ideal U) a
  rw [← hs]
  exact (le_iSup (fun b : I.ideal U => PrimeSpectrum.basicOpen b.1) a)
    (chartLocalizationι_range_base (I.ideal U) a ⟨x, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般の blowup の中心外の逆像開集合は blowup 全体で稠密。
方針：各点を標準チャートで表示し、正則な係数局所化の稠密像を中心外に含める。
規約：Stacks 081T、位相的稠密性。被約性・Noether 性は不要。
使われ方：固有な開部分スキームとして得た strict transform が全体に一致すること。
-/
theorem blowup_centerComplement_dense :
    Dense (blowupπ I ⁻¹ᵁ centerComplement I).carrier := by
  intro x
  obtain ⟨U, y, hy⟩ := exists_blowupAffineι I x
  let 𝒰 := affineBlowupChartCover (I.ideal U)
  let a : I.ideal U := 𝒰.idx y
  obtain ⟨z, hz⟩ := 𝒰.covers y
  change affineBlowupChartι (I.ideal U) a z = y at hz
  have hcl : blowupChartι I U a z ∈
      closure (blowupChartι I U a '' Set.range (chartLocalizationι (I.ideal U) a)) :=
    mem_closure_image (blowupChartι I U a).continuous.continuousAt
      (chartLocalizationι_denseRange (I.ideal U) a z)
  have hsub : blowupChartι I U a '' Set.range (chartLocalizationι (I.ideal U) a) ⊆
      (blowupπ I ⁻¹ᵁ centerComplement I).carrier := by
    rintro _ ⟨p, ⟨q, rfl⟩, rfl⟩
    exact blowupChartLocalization_range I U a ⟨q, rfl⟩
  have hpoint : blowupChartι I U a z = x := (congrArg (blowupAffineι I U) hz).trans hy
  rw [hpoint] at hcl
  exact closure_mono hsub hcl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
