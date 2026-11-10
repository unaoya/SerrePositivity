module

public import SerrePositivity.AlgebraicGeometry.NoetherianConstructibleStrata
public import SerrePositivity.AlgebraicGeometry.SmoothSectionOpenStratum
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
概要：Noether 基底上の滑らかなアフィン射で切断を通るファイバー成分の族は構成可能。
方針：既約閉部分を素イデアルで割った環のスペクトルにし、非空開部分上の表示を Noether 帰納に渡す。
規約：基底の閉部分には被約構造を入れる。
使われ方：切断を通るファイバー成分の開性。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits Set TopologicalSpace Topology
open scoped TensorProduct

/--
概要：滑らかなアフィン射の各ファイバーで切断を通る成分を合わせた集合は構成可能。
方針：各既約閉部分上で切断の成分が開になる非空開部分を取り、Noether 帰納を適用する。
規約：基底を Noether 環とする。
使われ方：Stacks 055N の滑らかなアフィン場合。
-/
theorem isConstructible_sectionComponentLocus_of_smooth
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] (s : B →ₐ[A] A) :
    IsConstructible (sectionComponentLocus (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom s.toRingHom))) := by
  let f : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let t : Spec (.of A) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom s.toRingHom)
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let : NoetherianSpace (Spec (.of A)) := inferInstanceAs (NoetherianSpace (PrimeSpectrum A))
  let : NoetherianSpace (Spec (.of B)) := inferInstanceAs (NoetherianSpace (PrimeSpectrum B))
  have hf : Continuous f := f.continuous
  change IsConstructible (sectionComponentLocus f t)
  refine isConstructible_of_open_over_irreducible_strata hf _ fun C hC => ?_
  let p : PrimeSpectrum A := ⟨PrimeSpectrum.vanishingIdeal (C : Set (Spec (.of A))),
    PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hC⟩
  let : p.asIdeal.IsPrime := p.isPrime
  let S := A ⧸ p.asIdeal
  let : IsDomain S := inferInstanceAs (IsDomain (A ⧸ p.asIdeal))
  let D := S ⊗[A] B
  let g : Spec (.of S) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A S))
  let i : Spec (.of D) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom)
  let f' : Spec (.of D) ⟶ Spec (.of S) := Spec.map (CommRingCat.ofHom (algebraMap S D))
  let t' : Spec (.of S) ⟶ Spec (.of D) :=
    Spec.map (CommRingCat.ofHom (baseChangeSection s : D →ₐ[S] S).toRingHom)
  have hPb : IsPullback i f' f g := isPullback_specTensor A B S
  let : IsClosedImmersion g :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal))
      Ideal.Quotient.mk_surjective
  let : IsClosedImmersion i :=
    MorphismProperty.of_isPullback hPb.flip (inferInstance : IsClosedImmersion g)
  have hLocus := preimage_sectionComponentLocus_of_isPullback_of_isEmbedding
    hPb i.isEmbedding t t' (spec_baseChangeSection_section s S) (spec_baseChangeSection_comm s S)
  obtain ⟨U', W', hU', hW'⟩ :=
    exists_open_stratum_sectionComponentLocus_of_smooth (baseChangeSection s : D →ₐ[S] S)
  change sectionComponentLocus f' t' ∩ f' ⁻¹' (U' : Set (Spec (.of S))) =
    (W' : Set (Spec (.of D))) ∩ f' ⁻¹' (U' : Set (Spec (.of S))) at hW'
  obtain ⟨V, hV, hVeq⟩ := g.isEmbedding.isInducing.isOpen_iff.mp U'.isOpen
  obtain ⟨W, hW, hWeq⟩ := i.isEmbedding.isInducing.isOpen_iff.mp W'.isOpen
  have hgRange : Set.range g = (C : Set (Spec (.of A))) := by
    change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal)) = _
    rw [range_comap_of_surjective S _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _).trans C.isClosed.closure_eq
  refine ⟨⟨V, hV⟩, ⟨W, hW⟩, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hU'
    refine ⟨g y, hgRange ▸ Set.mem_range_self y, ?_⟩
    exact (Set.ext_iff.mp hVeq y).mpr hy
  · ext x
    change (x ∈ sectionComponentLocus f t ∧ f x ∈ (C : Set (Spec (.of A))) ∩ V) ↔
      (x ∈ W ∧ f x ∈ (C : Set (Spec (.of A))) ∩ V)
    refine and_congr_left_iff.mpr fun hx => ?_
    have hxC : f x ∈ Set.range g := hgRange.symm ▸ hx.1
    obtain ⟨y, hy⟩ := hxC
    obtain ⟨z, hzx, hzy⟩ := Scheme.exists_preimage_of_isPullback hPb x y hy.symm
    change i z = x at hzx
    change f' z = y at hzy
    have hyV : g y ∈ V := by
      rw [hy]
      exact hx.2
    have hyU : y ∈ U' := (Set.ext_iff.mp hVeq y).mp hyV
    have hzU : f' z ∈ U' := hzy.symm ▸ hyU
    have hm := Set.ext_iff.mp hW' z
    subst x
    change z ∈ i ⁻¹' sectionComponentLocus f t ↔ z ∈ i ⁻¹' W
    rw [hLocus, hWeq]
    exact ⟨fun hz => (hm.mp ⟨hz, hzU⟩).1, fun hz => (hm.mpr ⟨hz, hzU⟩).1⟩

end SerrePositivity.AlgebraicGeometry
