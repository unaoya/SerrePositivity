module

public import SerrePositivity.AlgebraicGeometry.GeometricIntegralMarkerOpen
public import SerrePositivity.AlgebraicGeometry.SmoothFiniteMarkerOpen
public import SerrePositivity.AlgebraicGeometry.SmoothSectionComponentIntegral

/-!
概要：滑らかなアフィン族の幾何学的に連結なファイバーを、有限平坦な標識を使って幾何学的整な開部分に広げる。
方針：開部分を降下し、標識が全射となる基底に縮めて幾何学的整性を降下する。
規約：指定ファイバーは縮めた開部分に全体が含まれる。
使われ方：相対 Noether 正規化の先を、幾何学的整なファイバーを持つ滑らかな族へ縮める。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped TensorProduct

/--
概要：滑らかなアフィン射と有限平坦な標識があり、指定ファイバーが幾何学的に連結なら、
基底のアフィン開近傍上で、指定ファイバー全体を含み幾何学的に整な準コンパクト開がある。
方針：切断を通る成分の開部分を降下し、標識が全射となる近傍で幾何学的整性を比較する。
規約：標識は指定ファイバーと交わり、その幾何学的連結性はすべての体への底変換で仮定する。
使われ方：Stacks 057I の滑らかなアフィン場合と、057J への接続。
-/
theorem exists_geometricallyIntegral_open_of_smooth_finite_flat_marker
    {A B T : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [CommRing T]
    [Algebra A B] [Algebra A T] [Algebra.Smooth A B] [Module.Finite A T] [Module.Flat A T]
    (σ : B →ₐ[A] T) (a : PrimeSpectrum A)
    (hConn : ∀ (K : Type u) [Field K] [Algebra A K],
      (⊥ : PrimeSpectrum K).comap (algebraMap A K) = a →
        ConnectedSpace (PrimeSpectrum (K ⊗[A] B)))
    (hMark : ∃ z : PrimeSpectrum T, z.comap (algebraMap A T) = a) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
    ∃ (U : (Spec (.of A)).Opens) (V : (Spec (.of B)).Opens), IsAffineOpen U ∧ a ∈ U ∧
      IsCompact (V : Set (Spec (.of B))) ∧ f ⁻¹' ({a} : Set (Spec (.of A))) ⊆ V ∧
      ∃ hVU : V ≤ f ⁻¹ᵁ U, GeometricallyIntegral ((Spec (.of B)).homOfLE hVU ≫ f ∣_ U) := by
  let E := T ⊗[A] B
  let X := Spec (.of B)
  let S := Spec (.of A)
  let Y := Spec (.of E)
  let f : X ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g : Spec (.of T) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap A T))
  let i : Y ⟶ X :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] E).toRingHom)
  let fT : Y ⟶ Spec (.of T) := Spec.map (CommRingCat.ofHom (algebraMap T E))
  let τ : E →ₐ[T] T := AlgHom.liftEquiv A T B T σ
  let t : Spec (.of T) ⟶ Y := Spec.map (CommRingCat.ofHom τ.toRingHom)
  have hE : IsPullback i fT f g := isPullback_specTensor A B T
  obtain ⟨U, V, _, ha, _, _, hFull, heq⟩ :=
    exists_compact_open_of_smooth_finite_flat_marker σ a hConn hMark
  let : Flat g := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : LocallyOfFinitePresentation g :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr
        (Algebra.FinitePresentation.of_finiteType.mp (inferInstance : Algebra.FiniteType A T)))
  let O : S.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  have haO : a ∈ U ⊓ O := ⟨ha, hMark⟩
  obtain ⟨_, ⟨U', hU', rfl⟩, ha', hsub⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open haO (U ⊓ O).isOpen
  let U₀ : S.Opens := U'
  let : Surjective (g ∣_ U₀) := ⟨by
    intro x
    have hx : U₀.ι x ∈ U₀ :=
      (Set.ext_iff.mp (Scheme.Opens.range_ι U₀) (U₀.ι x)).mp (Set.mem_range_self x)
    obtain ⟨y, hy⟩ := (hsub hx).2
    obtain ⟨z, hz, _⟩ :=
      Scheme.exists_preimage_of_isPullback (isPullback_morphismRestrict g U₀) x y hy.symm
    exact ⟨z, hz⟩⟩
  let V' : X.Opens := V ⊓ f ⁻¹ᵁ U₀
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let : NoetherianSpace X := inferInstanceAs (NoetherianSpace (PrimeSpectrum B))
  let : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing A T
  let W : Y.Opens := ⟨sectionComponentLocus fT t, isOpen_sectionComponentLocus_of_smooth τ⟩
  let : GeometricallyIntegral (W.ι ≫ fT) :=
    geometricallyIntegral_sectionComponentLocus_of_smooth τ W rfl
  have hEq' : i ⁻¹ᵁ V' = W ⊓ (fT ≫ g) ⁻¹ᵁ U₀ := by
    apply SetLike.ext'
    ext z
    change (i z ∈ V ∧ f (i z) ∈ U₀) ↔ (z ∈ W ∧ g (fT z) ∈ U₀)
    have hz := Set.ext_iff.mp heq z
    change i z ∈ V ↔ z ∈ W ∧ f (i z) ∈ U at hz
    have hbase : f (i z) = g (fT z) := by
      have e := congrArg (fun k : Y ⟶ S => k z) hE.w
      simpa only [Scheme.Hom.comp_apply] using e
    rw [hz, ← hbase]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, (hsub h.2).1⟩, h.2⟩⟩
  refine ⟨U₀, V', hU', ha', NoetherianSpace.isCompact (V' : Set X), ?_, inf_le_right, ?_⟩
  · intro x hx
    refine ⟨hFull hx, ?_⟩
    have hx' : f x = a := hx
    change f x ∈ U₀
    rw [hx']
    exact ha'
  · exact geometricallyIntegral_marker_open_of_surjective_restrict
      hE U₀ V' W inf_le_right hEq'

end SerrePositivity.AlgebraicGeometry
