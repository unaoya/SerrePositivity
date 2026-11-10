module

public import SerrePositivity.AlgebraicGeometry.SmoothSectionComponentConstructible
public import SerrePositivity.AlgebraicGeometry.SectionComponentTensorBaseChange
public import SerrePositivity.AlgebraicGeometry.NormalLocalSpecialization
public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet

/-!
概要：滑らかなアフィン射の切断を通るファイバー成分の族は開。
方針：整閉局所整域に沿って特殊化を表し、二つの切断を閉点と生成点で比較する。
規約：Noether 性は構成可能性を示す段階で使う。
使われ方：有限局所自由な標識から幾何学的整な成分を広げる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

private theorem mem_sectionComponentLocus_iff_sectionPointInTensor
    {A B V L : Type u} [CommRing A] [CommRing B] [CommRing V] [Field L]
    [Algebra A B] [Algebra A V] [Algebra A L] [Algebra V L] [IsScalarTower A V L]
    [Algebra.FiniteType A B] (s : B →ₐ[A] A) (v : B →ₐ[A] V) :
    (⊥ : PrimeSpectrum L).comap ((algebraMap V L).comp v.toRingHom) ∈
      sectionComponentLocus (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom s.toRingHom)) ↔
    sectionPointInTensor L (AlgHom.liftEquiv A V B V v) ∈
      connectedComponent (sectionPointInTensor L
        (baseChangeSection s : V ⊗[A] B →ₐ[V] V)) := by
  let E := V ⊗[A] B
  let t : E →ₐ[V] V := AlgHom.liftEquiv A V B V v
  let s' : E →ₐ[V] V := baseChangeSection s
  let e := Algebra.TensorProduct.cancelBaseChange A V L L B
  let D := L ⊗[A] B
  let T := L ⊗[V] E
  let j : B →ₐ[A] D := Algebra.TensorProduct.includeRight
  let q := (⊥ : PrimeSpectrum L).comap ((algebraMap V L).comp v.toRingHom)
  let p := q.comap (algebraMap A B)
  let x' := (⊥ : PrimeSpectrum L).comap (baseChangeSection t : T →ₐ[L] L).toRingHom
  let x := x'.comap e.symm.toRingHom
  have hp : RingHom.ker (algebraMap A L) = p.asIdeal := by
    ext a
    change algebraMap A L a = 0 ↔ algebraMap V L (v (algebraMap A B a)) = 0
    rw [v.commutes, IsScalarTower.algebraMap_apply A V L]
  have hx : x.comap j.toRingHom = q := by
    apply PrimeSpectrum.ext
    ext b
    change baseChangeSection t (e.symm ((1 : L) ⊗ₜ[A] b)) = 0 ↔ algebraMap V L (v b) = 0
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul, baseChangeSection_tmul, one_mul]
    have h : t ((1 : V) ⊗ₜ[A] b) = v b := by
      change (1 : V) • v b = _
      rw [one_smul]
    rw [h]
  have hmem := mem_sectionComponentLocus_iff_of_field_extension s p hp x
  change x.comap j.toRingHom ∈ _ ↔ _ at hmem
  rw [hx] at hmem
  let qD := (⊥ : PrimeSpectrum L).comap (baseChangeSection s : D →ₐ[L] L).toRingHom
  let qT := (⊥ : PrimeSpectrum L).comap (baseChangeSection s' : T →ₐ[L] L).toRingHom
  have hqT : qT = qD.comap e.toRingHom := by
    change (⊥ : PrimeSpectrum L).comap (baseChangeSection s' : T →ₐ[L] L).toRingHom = _
    rw [baseChangeSection_comp_cancelBaseChange]
    rfl
  let H := PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
  have hxH : H.symm x = x' := H.symm_apply_apply x'
  have hqH : H.symm qD = qT := hqT.symm
  change q ∈ _ ↔ _
  refine hmem.trans ?_
  change x ∈ connectedComponent qD ↔
    sectionPointInTensor L t ∈ connectedComponent (sectionPointInTensor L s')
  have hC : x ∈ connectedComponent qD ↔ x' ∈ connectedComponent qT := by
    constructor
    · intro h
      simpa only [hxH, hqH] using H.symm.continuous.mapsTo_connectedComponent qD h
    · intro h
      have hh : H.symm x ∈ connectedComponent (H.symm qD) := by simpa only [hxH, hqH] using h
      simpa only [H.apply_symm_apply] using H.continuous.mapsTo_connectedComponent (H.symm qD) hh
  let C := PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.comm V L E).toRingEquiv
  have htC : C x' = sectionPointInTensor L t := by
    have ht := sectionPointInTensor_comm (F := L) t
    change x' = C.symm (sectionPointInTensor L t) at ht
    rw [ht, C.apply_symm_apply]
  have hsC : C qT = sectionPointInTensor L s' := by
    have hs := sectionPointInTensor_comm (F := L) s'
    change qT = C.symm (sectionPointInTensor L s') at hs
    rw [hs, C.apply_symm_apply]
  refine hC.trans ⟨?_, ?_⟩
  · intro h
    simpa only [htC, hsC] using C.continuous.mapsTo_connectedComponent qT h
  · intro h
    have hh : C x' ∈ connectedComponent (C qT) := by simpa only [htC, hsC] using h
    simpa only [C.symm_apply_apply] using C.symm.continuous.mapsTo_connectedComponent (C qT) hh

/--
概要：滑らかなアフィン射で切断を通るファイバー成分の集合は生成化で保たれる。
方針：素イデアルの包含を整閉局所整域の二点で実現し、そこで二つの切断を比較する。
規約：一般点は分数体、閉点は局所環の剰余体で調べる。
使われ方：構成可能な成分の族を開集合と同定する。
-/
theorem stableUnderGeneralization_sectionComponentLocus_of_smooth
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (s : B →ₐ[A] A) :
    StableUnderGeneralization (sectionComponentLocus (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom s.toRingHom))) := by
  intro q p hpq hq
  let P : PrimeSpectrum B := p
  let Q : PrimeSpectrum B := q
  let : P.asIdeal.IsPrime := P.isPrime
  let : Q.asIdeal.IsPrime := Q.isPrime
  have hpq' : P.asIdeal ≤ Q.asIdeal := (PrimeSpectrum.le_iff_specializes P Q).mpr hpq
  obtain ⟨V, _, _, _, _, g, hp, hq'⟩ :=
    exists_normalLocalDomain_of_prime_le P.asIdeal Q.asIdeal hpq'
  let : Algebra A V := (g.comp (algebraMap A B)).toAlgebra
  let v : B →ₐ[A] V := ⟨g, fun _ => rfl⟩
  let E := V ⊗[A] B
  let t : E →ₐ[V] V := AlgHom.liftEquiv A V B V v
  let s' : E →ₐ[V] V := baseChangeSection s
  let k := IsLocalRing.ResidueField V
  let K := FractionRing V
  have hqk : (⊥ : PrimeSpectrum k).comap ((algebraMap V k).comp v.toRingHom) = q := by
    apply PrimeSpectrum.ext
    change RingHom.ker ((IsLocalRing.residue V).comp g) = q.asIdeal
    rw [← RingHom.comap_ker, IsLocalRing.ker_residue, hq']
  have hpK : (⊥ : PrimeSpectrum K).comap ((algebraMap V K).comp v.toRingHom) = p := by
    apply PrimeSpectrum.ext
    change RingHom.ker ((algebraMap V K).comp g) = p.asIdeal
    rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective V K), hp]
  have hc : sectionPointInTensor k t ∈ connectedComponent (sectionPointInTensor k s') :=
    (mem_sectionComponentLocus_iff_sectionPointInTensor (L := k) s v).mp (hqk.symm ▸ hq)
  have hg := sectionPointInTensor_mem_genericComponent_of_mem_closedComponent
    (K := K) s' t hc
  exact hpK ▸ (mem_sectionComponentLocus_iff_sectionPointInTensor (L := K) s v).mpr hg

/--
概要：Noether 基底上の滑らかなアフィン射で、切断を通るファイバー成分の族は開。
方針：構成可能性と生成化に関する安定性を合わせる。
規約：集合は始域のスペクトル上で取る。
使われ方：標識の切断から、幾何学的整なファイバーを持つ開部分を選ぶ。
-/
theorem isOpen_sectionComponentLocus_of_smooth
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] (s : B →ₐ[A] A) :
    IsOpen (sectionComponentLocus (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom s.toRingHom))) :=
  PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible
    (stableUnderGeneralization_sectionComponentLocus_of_smooth s)
    (isConstructible_sectionComponentLocus_of_smooth s)

end SerrePositivity.AlgebraicGeometry
