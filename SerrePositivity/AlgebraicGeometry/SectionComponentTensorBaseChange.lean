module

public import SerrePositivity.AlgebraicGeometry.SmoothSectionComponentFieldExtension

/-!
概要：アフィン射の切断を通るファイバー成分の集合を、任意のアフィン底変換と比較する。
方針：各点で剰余体に移り、二段階のテンソル積を一段階にして体拡大の比較を使う。
規約：テンソル積の左に底変換先を置く。
使われ方：有限局所自由な標識の自己ファイバー積で、成分の二つの逆像を比較する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

/--
概要：二度底変換した切断は、テンソル積の標準同型で一度底変換した切断に一致する。
方針：二重の単純テンソルで評価を比較する。
規約：基底変更の順にテンソル積の左へ追加する。
使われ方：剰余体上での切断を通る成分の比較。
-/
theorem baseChangeSection_comp_cancelBaseChange
    {A B V L : Type u} [CommRing A] [CommRing B] [CommRing V] [CommRing L]
    [Algebra A B] [Algebra A V] [Algebra A L] [Algebra V L] [IsScalarTower A V L]
    (s : B →ₐ[A] A) :
    (baseChangeSection (baseChangeSection s : V ⊗[A] B →ₐ[V] V) :
        L ⊗[V] (V ⊗[A] B) →ₐ[L] L) =
      (baseChangeSection s : L ⊗[A] B →ₐ[L] L).comp
        (Algebra.TensorProduct.cancelBaseChange A V L L B).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro a b
  induction b using TensorProduct.inductionOn with
  | tmul c b =>
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      Algebra.TensorProduct.cancelBaseChange_tmul, baseChangeSection_tmul,
      Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
    ac_rfl
  | add b c hb hc => rw [TensorProduct.tmul_add, map_add, map_add, hb, hc]

/--
概要：アフィン底変換後の切断を通る成分の族は、元の成分の族の逆像。
方針：底変換後の各点を剰余体上に持ち上げ、元の基底の剰余体の拡大として比較する。
規約：元のアフィン射を有限型とする。
使われ方：Stacks 057I で有限標識の二つの射による成分の逆像を同定する。
-/
theorem preimage_sectionComponentLocus_specTensor
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (s : B →ₐ[A] A) (V : Type u) [CommRing V] [Algebra A V] :
    PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] V ⊗[A] B).toRingHom ⁻¹'
      sectionComponentLocus (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom s.toRingHom)) =
      sectionComponentLocus (Spec.map (CommRingCat.ofHom (algebraMap V (V ⊗[A] B))))
        (Spec.map (CommRingCat.ofHom (baseChangeSection s : V ⊗[A] B →ₐ[V] V).toRingHom)) := by
  let E := V ⊗[A] B
  let v : E →ₐ[V] V := baseChangeSection s
  let i : B →ₐ[A] E := Algebra.TensorProduct.includeRight
  let C := sectionComponentLocus (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (Spec.map (CommRingCat.ofHom s.toRingHom))
  let C' := sectionComponentLocus (Spec.map (CommRingCat.ofHom (algebraMap V E)))
    (Spec.map (CommRingCat.ofHom v.toRingHom))
  change PrimeSpectrum.comap i.toRingHom ⁻¹' C = C'
  ext x
  let p := x.comap (algebraMap V E)
  let L := p.asIdeal.ResidueField
  let T := L ⊗[V] E
  let D := L ⊗[A] B
  let e : T ≃ₐ[L] D := Algebra.TensorProduct.cancelBaseChange A V L L B
  let j : E →ₐ[V] T := Algebra.TensorProduct.includeRight
  let k : B →ₐ[A] D := Algebra.TensorProduct.includeRight
  have hx : x ∈ Set.range (PrimeSpectrum.comap j.toRingHom) := by
    rw [range_comap_includeRight_residueField (B := E) p]
    exact Set.mem_singleton _
  obtain ⟨z, hz⟩ := hx
  let w := z.comap e.symm.toRingHom
  have hw : w.comap k.toRingHom = x.comap i.toRingHom := by
    have h : e.symm.toRingHom.comp k.toRingHom = j.toRingHom.comp i.toRingHom := by
      apply RingHom.ext
      intro b
      change e.symm ((1 : L) ⊗ₜ[A] b) = (1 : L) ⊗ₜ[V] ((1 : V) ⊗ₜ[A] b)
      exact Algebra.TensorProduct.cancelBaseChange_symm_tmul _ _ _ _ _ _ _
    rw [show w = z.comap e.symm.toRingHom from rfl, ← PrimeSpectrum.comap_comp_apply, h,
      PrimeSpectrum.comap_comp_apply, hz]
  have hV := preimage_sectionComponentLocus_spec_residueField v p
  rw [← sectionPointInTensor_comm] at hV
  let qD := (⊥ : PrimeSpectrum L).comap (baseChangeSection s : D →ₐ[L] L).toRingHom
  let qT := (⊥ : PrimeSpectrum L).comap (baseChangeSection v : T →ₐ[L] L).toRingHom
  have hq : qT = qD.comap e.toRingHom := by
    change (⊥ : PrimeSpectrum L).comap (baseChangeSection v : T →ₐ[L] L).toRingHom = _
    rw [baseChangeSection_comp_cancelBaseChange]
    rfl
  let H := PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
  have hHZ : H z = w := rfl
  have hHQ : H qT = qD := by
    rw [hq]
    exact H.apply_symm_apply qD
  have hC : w ∈ connectedComponent qD ↔ z ∈ connectedComponent qT := by
    rw [← hHZ, ← hHQ]
    constructor
    · intro h
      simpa only [H.symm_apply_apply] using H.symm.continuous.mapsTo_connectedComponent (H qT) h
    · intro h
      exact H.continuous.mapsTo_connectedComponent qT h
  let pA := (⊥ : PrimeSpectrum L).comap (algebraMap A L)
  have hLA : RingHom.ker (algebraMap A L) = pA.asIdeal := rfl
  change x.comap i.toRingHom ∈ C ↔ x ∈ C'
  rw [← hw]
  refine (mem_sectionComponentLocus_iff_of_field_extension s pA hLA w).trans (hC.trans ?_)
  have hm := Set.ext_iff.mp hV z
  change z.comap j.toRingHom ∈ C' ↔ z ∈ connectedComponent qT at hm
  rw [hz] at hm
  exact hm.symm

end SerrePositivity.AlgebraicGeometry
