module

public import SerrePositivity.KST.SchemeLemmas.ChartBoundaryRegular
public import SerrePositivity.KST.SchemeLemmas.ChartGluing
public import SerrePositivity.KST.SchemeLemmas.SchemeBlowupAffine

/-!
# 非零因子の境界基本開の blowup 上の稠密性

## 概要
中心の補集合に一致しない基本開でも、境界元が非零因子なら blowup 上の逆像は稠密となる。

## 方針
各実際のチャートで非零因子性を保ち、一元局所化の稠密像を基本開へ移す。

## 規約
中心の有限生成性や Noether 性は不要。中心外の稠密性との無証明の置換は行わない。

## 使われ方
論文 補題 3.3、公理 (6) の加群平坦化で得る境界 D(r) から strict transform の全射性へ接続する。
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

/-- 概要：非零因子が定める基本開は素スペクトルで稠密（論文 補題 3.3）。
方針：一元局所化の環準同型の単射性と Spec の稠密像の判定を使う。
規約：零環も含み、Noether 性や被約性は要求しない。
使われ方：全 blowup チャートの境界基本開の稠密性。 -/
theorem basicOpen_dense_of_nonZeroDivisor {R : Type u} [CommRing R] (r : R)
    (hr : r ∈ nonZeroDivisors R) : Dense (PrimeSpectrum.basicOpen r).carrier := by
  have hd : DenseRange (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp
      (IsLocalization.injective (Localization.Away r) (Submonoid.powers_le.mpr hr))]
    exact bot_le
  have he : Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) =
      (PrimeSpectrum.basicOpen r).carrier :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away r) r
  exact he ▸ (hd : Dense (Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r)))))

set_option backward.isDefEq.respectTransparency false in
/-- 概要：アフィン blowup の境界基本開の逆像は稠密（論文 補題 3.3）。
方針：非零因子の全チャートでの保存と、各点の実際の標準チャート表示を使う。
規約：D(r) が中心の補集合と一致する仮定は不要。
使われ方：平坦化に用いた境界から全射性の稠密開判定へ渡す。 -/
theorem affineBlowup_boundary_dense {R : Type u} [CommRing R] (I : Ideal R) (r : R)
    (hr : r ∈ nonZeroDivisors R) :
    Dense (affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen r).carrier := by
  intro x
  let 𝒰 := affineBlowupChartCover I
  obtain ⟨z, hz⟩ := 𝒰.covers x
  let a : I := 𝒰.idx x
  change affineBlowupChartι I a z = x at hz
  have hd := basicOpen_dense_of_nonZeroDivisor (chartBaseMap I a r)
    (chartBaseMap_nonZeroDivisors I a hr)
  have hcl : affineBlowupChartι I a z ∈
      closure (affineBlowupChartι I a '' (PrimeSpectrum.basicOpen (chartBaseMap I a r)).carrier) :=
    mem_closure_image (affineBlowupChartι I a).continuous.continuousAt (hd z)
  have hsub : affineBlowupChartι I a '' (PrimeSpectrum.basicOpen (chartBaseMap I a r)).carrier ⊆
      (affineBlowupπ I ⁻¹ᵁ PrimeSpectrum.basicOpen r).carrier := by
    rintro _ ⟨w, hw, rfl⟩
    change (affineBlowupChartι I a ≫ affineBlowupπ I) w ∈ PrimeSpectrum.basicOpen r
    have he : affineBlowupChartι I a ≫ affineBlowupπ I =
        Spec.map (CommRingCat.ofHom (chartBaseMap I a)) := affineBlowupChartIso_inv_ι_π I a
    have hx : (Spec.map (CommRingCat.ofHom (chartBaseMap I a))) w ∈
        PrimeSpectrum.basicOpen r := hw
    exact (congrArg (fun k ↦ k w) he).symm ▸ hx
  exact hz ▸ closure_mono hsub hcl

set_option backward.isDefEq.respectTransparency false in
/-- 概要：アフィン基底の実際の blowup 上で非零因子の境界基本開の逆像は稠密（補題 3.3）。
方針：全体のアフィンモデルからの全射と構造射の可換性で稠密性を移す。
規約：中心の補集合との一致や中心の有限生成性は不要。
使われ方：global strict transform の有限性と稠密開の全射性から全射性を得る。 -/
theorem blowup_boundary_dense_of_isAffine {S : Scheme.{u}} [IsAffine S]
    (J : S.IdealSheafData) (r : Γ(S, ⊤)) (hr : r ∈ nonZeroDivisors Γ(S, ⊤)) :
    Dense (blowupπ J ⁻¹ᵁ S.basicOpen r).carrier := by
  let U : S.affineOpens := ⟨⊤, isAffineOpen_top S⟩
  have hs : Function.Surjective (blowupAffineι J U) := by
    rw [← Set.range_eq_univ, blowupAffineι_range]
    simp [U]
  have hd := affineBlowup_boundary_dense (J.ideal U) r hr
  intro x
  obtain ⟨y, hy⟩ := hs x
  have hcl : blowupAffineι J U y ∈ closure
      (blowupAffineι J U '' (affineBlowupπ (J.ideal U) ⁻¹ᵁ PrimeSpectrum.basicOpen r).carrier) :=
    mem_closure_image (blowupAffineι J U).continuous.continuousAt (hd y)
  have hsub : blowupAffineι J U ''
      (affineBlowupπ (J.ideal U) ⁻¹ᵁ PrimeSpectrum.basicOpen r).carrier ⊆
        (blowupπ J ⁻¹ᵁ S.basicOpen r).carrier := by
    rintro _ ⟨z, hz, rfl⟩
    change (blowupAffineι J U ≫ blowupπ J) z ∈ S.basicOpen r
    rw [blowupAffineι_π]
    change affineBlowupπ (J.ideal U) z ∈ U.2.fromSpec ⁻¹ᵁ S.basicOpen r
    rw [U.2.fromSpec_preimage_basicOpen]
    exact hz
  exact hy ▸ closure_mono hsub hcl

end SerrePositivity.KST.Descent
