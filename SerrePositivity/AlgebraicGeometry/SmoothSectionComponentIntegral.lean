module

public import SerrePositivity.AlgebraicGeometry.SectionComponentTensorBaseChange
public import SerrePositivity.AlgebraicGeometry.SmoothConnectedDomain
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
概要：切断を通る成分の族が開なら、滑らかなアフィン射をその開部分に制限した射は幾何学的に整。
方針：任意の体へ底変換し、切断を通る成分を表す主開が連結かつ滑らかであることを使う。
規約：成分の族の開性は仮定として受け取る。
使われ方：有限局所自由な標識上で得た成分を幾何学的整な開部分として降下する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

/--
概要：滑らかなアフィン射の切断を通る成分が開部分をなすとき、その開部分は幾何学的に整なファイバーを持つ。
方針：体上では切断を通る連結成分は開閉で、その局所化環は連結かつ滑らかなので整域。
規約：すべての体への底変換を同じテンソル積表示で扱う。
使われ方：Stacks 057I と 057J の滑らかな場合。
-/
theorem geometricallyIntegral_sectionComponentLocus_of_smooth
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (s : B →ₐ[A] A) (W : (Spec (.of B)).Opens)
    (hW : (W : Set (Spec (.of B))) =
      sectionComponentLocus (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom s.toRingHom))) :
    GeometricallyIntegral (W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  rw [GeometricallyIntegral.eq_geometrically, geometrically_iff_of_commRing]
  intro F _ _ Y fst snd hY
  let D := F ⊗[A] B
  let f : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g : Spec (.of F) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A F))
  let i : Spec (.of D) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom)
  let f' : Spec (.of D) ⟶ Spec (.of F) := Spec.map (CommRingCat.ofHom (algebraMap F D))
  let v : D →ₐ[F] F := baseChangeSection s
  let t' : Spec (.of F) ⟶ Spec (.of D) := Spec.map (CommRingCat.ofHom v.toRingHom)
  let p := (⊥ : PrimeSpectrum F).comap v.toRingHom
  have hPb : IsPullback i f' f g := isPullback_specTensor A B F
  have hComp : sectionComponentLocus f' t' = connectedComponent p := by
    ext x
    change x ∈ connectedComponentIn (f' ⁻¹' {f' x}) (t' (f' x)) ↔ _
    have hf : f' x = (⊥ : PrimeSpectrum F) := Subsingleton.elim _ _
    have hu : f' ⁻¹' {f' x} = Set.univ := Set.eq_univ_of_forall fun y =>
      Set.mem_singleton_iff.mpr (Subsingleton.elim (f' y) (f' x))
    rw [hu, connectedComponentIn_univ, hf]
    rfl
  let : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing F D
  obtain ⟨e, _, he⟩ := PrimeSpectrum.isClopen_iff.mp
    (isClopen_connectedComponent_of_noetherianSpace p)
  let R := Localization.Away e
  let j : Spec (.of R) ⟶ Spec (.of D) := Spec.map (CommRingCat.ofHom (algebraMap D R))
  let : IsOpenImmersion j := IsOpenImmersion.of_isLocalization e
  have hj : Set.range j = connectedComponent p := by
    change Set.range (PrimeSpectrum.comap (algebraMap D R)) = _
    exact (PrimeSpectrum.localization_away_comap_range R e).trans he.symm
  let : ConnectedSpace (PrimeSpectrum R) := by
    let E := (PrimeSpectrum.localization_away_isOpenEmbedding R e).isEmbedding.toHomeomorph
    rw [E.connectedSpace_iff, ← isConnected_iff_connectedSpace]
    have hj' : Set.range (PrimeSpectrum.comap (algebraMap D R)) = connectedComponent p := hj
    exact hj'.symm ▸ isConnected_connectedComponent
  let : Algebra.Smooth D R := Algebra.Smooth.of_isLocalization_Away e
  let : Algebra.Smooth F R := Algebra.Smooth.comp F D R
  let : IsDomain R := isDomain_of_connected_smooth_over_field (k := F)
  have hRange : Set.range (pullback.snd W.ι i) = connectedComponent p := by
    rw [IsOpenImmersion.range_pullbackSnd W.ι i, Scheme.Opens.opensRange_ι]
    change i ⁻¹' (W : Set (Spec (.of B))) = _
    rw [hW]
    exact (preimage_sectionComponentLocus_specTensor s F).trans hComp
  let J := IsOpenImmersion.isoOfRangeEq j (pullback.snd W.ι i) (hj.trans hRange.symm)
  let P := (IsPullback.of_hasPullback W.ι i).paste_vert hPb
  exact IsIntegral.of_isIso (J ≪≫ P.isoPullback ≪≫ hY.isoPullback.symm).hom

end SerrePositivity.AlgebraicGeometry
