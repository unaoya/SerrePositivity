module

public import SerrePositivity.AlgebraicGeometry.AffineSectionComponentLocus
public import SerrePositivity.AlgebraicGeometry.AffineFiberComponentBaseChange

/-!
概要：切断を通るファイバー成分を、点の剰余体の任意の拡大体上で比較する。
方針：剰余体上の成分の逆像を、切断の有理点を使って一つの連結成分と同定する。
規約：底変換先をテンソル積の左に置く。
使われ方：切断を通る成分の集合が生成化で保たれること。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

/--
概要：剰余体の拡大上の点が底変換した切断を通る成分に属する条件は、元の点の条件と同じ。
方針：底変換を剰余体経由に分解し、切断の有理点を含む連結成分を比較する。
規約：基底から体への写像の核で、もとのファイバーを指定する。
使われ方：整閉局所整域の一般点と閉点から、もとの始域へ成分の比較を戻す。
-/
theorem mem_sectionComponentLocus_iff_of_field_extension
    {A B L : Type u} [CommRing A] [CommRing B] [Field L] [Algebra A B] [Algebra A L]
    [Algebra.FiniteType A B] (s : B →ₐ[A] A) (p : PrimeSpectrum A)
    (hp : RingHom.ker (algebraMap A L) = p.asIdeal) (x : PrimeSpectrum (L ⊗[A] B)) :
    x.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] L ⊗[A] B).toRingHom ∈
      sectionComponentLocus (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom s.toRingHom)) ↔
      x ∈ connectedComponent
        ((⊥ : PrimeSpectrum L).comap (baseChangeSection s : L ⊗[A] B →ₐ[L] L).toRingHom) := by
  let F := p.asIdeal.ResidueField
  let σ : F →+* L := Ideal.ResidueField.lift p.asIdeal (algebraMap A L) hp.ge
    (fun b hb => isUnit_iff_ne_zero.mpr fun h =>
      hb (hp ▸ (show b ∈ RingHom.ker (algebraMap A L) from h)))
  let : Algebra F L := σ.toAlgebra
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun b =>
    (Ideal.ResidueField.lift_algebraMap p.asIdeal (algebraMap A L) _ _ b).symm
  let E := F ⊗[A] B
  let D := L ⊗[A] B
  let T := L ⊗[F] E
  let e : T ≃ₐ[L] D := Algebra.TensorProduct.cancelBaseChange A F L L B
  let j : E →ₐ[F] T := Algebra.TensorProduct.includeRight
  let iF : B →ₐ[A] E := Algebra.TensorProduct.includeRight
  let iL : B →ₐ[A] D := Algebra.TensorProduct.includeRight
  let vF : E →ₐ[F] F := baseChangeSection s
  let vL : D →ₐ[L] L := baseChangeSection s
  let qF := (⊥ : PrimeSpectrum F).comap vF.toRingHom
  let qL := (⊥ : PrimeSpectrum L).comap vL.toRingHom
  let qT := qL.comap e.toRingHom
  have hIncl : (e.toRingHom.comp j.toRingHom).comp iF.toRingHom = iL.toRingHom := by
    apply RingHom.ext
    intro b
    change e (1 ⊗ₜ[F] ((1 : F) ⊗ₜ[A] b)) = 1 ⊗ₜ[A] b
    have h := Algebra.TensorProduct.cancelBaseChange_tmul A F L L B (1 : L) (1 : F) b
    exact h.trans (by rw [one_smul])
  have hEval : (vL.toRingHom.comp e.toRingHom).comp j.toRingHom =
      (algebraMap F L).comp vF.toRingHom := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      change vL (e (1 ⊗ₜ[F] (a ⊗ₜ[A] b))) = algebraMap F L (vF (a ⊗ₜ[A] b))
      have h : e (1 ⊗ₜ[F] (a ⊗ₜ[A] b)) = (a • (1 : L)) ⊗ₜ[A] b :=
        Algebra.TensorProduct.cancelBaseChange_tmul A F L L B 1 a b
      rw [h]
      change baseChangeSection s ((a • (1 : L)) ⊗ₜ[A] b) =
        algebraMap F L (baseChangeSection s (a ⊗ₜ[A] b))
      simp only [Algebra.smul_def, mul_one, baseChangeSection_tmul, map_mul,
        ← IsScalarTower.algebraMap_apply]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have hq : qT.comap j.toRingHom = qF := by
    change ((⊥ : PrimeSpectrum L).comap vL.toRingHom |>.comap e.toRingHom).comap j.toRingHom = _
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, ← RingHom.comp_assoc,
      hEval, PrimeSpectrum.comap_comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  let : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing F E
  let : ConnectedSpace (PrimeSpectrum (F ⊗[F] L)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.lid F L).toRingEquiv).connectedSpace_iff.mpr inferInstance
  have hT : PrimeSpectrum.comap j.toRingHom ⁻¹' connectedComponent qF =
      connectedComponent qT :=
    preimage_connectedComponent_eq_of_tensor_connected_point vF qT hq
  let C : Set (PrimeSpectrum B) :=
    sectionComponentLocus (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom s.toRingHom))
  have hF := preimage_sectionComponentLocus_spec_residueField s p
  rw [← sectionPointInTensor_comm] at hF
  change PrimeSpectrum.comap iF.toRingHom ⁻¹' C = connectedComponent qF at hF
  have hX : (x.comap e.toRingHom |>.comap j.toRingHom).comap iF.toRingHom =
      x.comap iL.toRingHom := by
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
      ← RingHom.comp_assoc, hIncl]
  have hLocus :
      x.comap iL.toRingHom ∈ C ↔ x.comap e.toRingHom ∈ connectedComponent qT := by
    rw [← hX]
    change x.comap e.toRingHom ∈ PrimeSpectrum.comap j.toRingHom ⁻¹'
      (PrimeSpectrum.comap iF.toRingHom ⁻¹' C) ↔ _
    rw [hF, hT]
  let H := PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
  refine hLocus.trans ⟨?_, ?_⟩
  · intro hx
    have h := H.continuous.mapsTo_connectedComponent qT hx
    change H (H.symm x) ∈ connectedComponent (H (H.symm qL)) at h
    simpa only [H.apply_symm_apply] using h
  · intro hx
    exact H.symm.continuous.mapsTo_connectedComponent qL hx

end SerrePositivity.AlgebraicGeometry
