module

public import SerrePositivity.AlgebraicGeometry.SchemeVCoverSpecializations
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
概要：一般点を含む開の逆像の閉包は、非 Noether 基底でも v 被覆の基底へ全射。
方針：特殊化の持ち上げの証明で使う一般化の選択を、独立した入力に分ける。
規約：基底の Noether 性や元の射の固有性を仮定しない。
使われ方：Rydh 3.10 の非 Noether affine 基底で、引き戻した狭義変換の全射性を回収する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
universe u

/-- 開の点からの特殊化が全点を覆うなら、v 被覆の開部分のスキーム論的像は基底へ全射。 -/
theorem surjective_openImage_of_vCover_of_specializations {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : IsSchemeVCover f) (U : Y.Opens)
    (hU : ∀ y : Y, ∃ p : Y, p ∈ U ∧ p ⤳ y) [QuasiCompact (f ⁻¹ᵁ U).ι] :
    Surjective ((f ⁻¹ᵁ U).ι.imageι ≫ f) := by
  constructor
  intro y
  obtain ⟨p, hp, hpy⟩ := hU y
  obtain ⟨x, z, hxz, hxp, hzy⟩ := hf.liftsSpecializations hpy
  have hx : x ∈ f ⁻¹ᵁ U := by change f x ∈ U; rwa [hxp]
  have hxrange : x ∈ Set.range (f ⁻¹ᵁ U).ι := ⟨⟨x, hx⟩, rfl⟩
  have hz : z ∈ closure (Set.range (f ⁻¹ᵁ U).ι) :=
    closure_mono (Set.singleton_subset_iff.mpr hxrange) hxz.mem_closure
  have hr : Set.range (f ⁻¹ᵁ U).ι.imageι = closure (Set.range (f ⁻¹ᵁ U).ι) := by
    change Set.range (f ⁻¹ᵁ U).ι.ker.subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
  obtain ⟨w, hw⟩ := hr.symm ▸ hz
  exact ⟨w, by change f ((f ⁻¹ᵁ U).ι.imageι w) = y; rw [hw, hzy]⟩

/-- アフィン基底の極小素点を全て含む開に対する、スキーム論的像の全射性。 -/
theorem surjective_openImage_of_vCover_affine_of_contains_minimalPrimes
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (hf : IsSchemeVCover f)
    (U : (Spec R).Opens) (hU : ∀ q : PrimeSpectrum R,
      q.asIdeal ∈ minimalPrimes R → q ∈ U) [QuasiCompact (f ⁻¹ᵁ U).ι] :
    Surjective ((f ⁻¹ᵁ U).ι.imageι ≫ f) := by
  apply surjective_openImage_of_vCover_of_specializations f hf U
  intro y
  have : y.asIdeal.IsPrime := y.isPrime
  obtain ⟨p, hp, hpy⟩ := Ideal.exists_minimalPrimes_le (J := y.asIdeal) bot_le
  let q : PrimeSpectrum R := ⟨p, hp.1.1⟩
  exact ⟨q, hU q hp, (PrimeSpectrum.le_iff_specializes q y).mp hpy⟩

/-- 極小素点集合が準コンパクトなら、それを含む開の内側に準コンパクト稠密開を選べる。 -/
theorem exists_compact_denseOpen_of_contains_minimalPrimes
    (R : CommRingCat.{u})
    (hmin : IsCompact {q : PrimeSpectrum R | q.asIdeal ∈ minimalPrimes R})
    (V : (Spec R).Opens) (hV : ∀ q : PrimeSpectrum R,
      q.asIdeal ∈ minimalPrimes R → q ∈ V) :
    ∃ U : (Spec R).Opens, IsCompact U.carrier ∧ Dense U.carrier ∧ U ≤ V ∧
      ∀ q : PrimeSpectrum R, q.asIdeal ∈ minimalPrimes R → q ∈ U := by
  obtain ⟨W, hWc, hWo, hMW, hWV⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hmin V.isOpen hV
  refine ⟨⟨W, hWo⟩, hWc, ?_, hWV, hMW⟩
  intro y
  have : y.asIdeal.IsPrime := y.isPrime
  obtain ⟨p, hp, hpy⟩ := Ideal.exists_minimalPrimes_le (J := y.asIdeal) bot_le
  let q : PrimeSpectrum R := ⟨p, hp.1.1⟩
  exact closure_mono (Set.singleton_subset_iff.mpr (hMW hp))
    ((PrimeSpectrum.le_iff_mem_closure q y).mp hpy)

end SerrePositivity.AlgebraicGeometry
