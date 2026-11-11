module

public import SerrePositivity.AlgebraicGeometry.AffineSectionComponentLocus

/-!
概要：整基底上の滑らかなアフィン射で、切断を通る成分の族を非空開部分上で開集合として表示する。
方針：生成成分を定める冪等元の主開を、局所化から元の始域へ移す。
規約：基底と始域を同じ局所化で縮める。
使われ方：Stacks 055N の滑らかな場合の Noether 帰納。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

/--
概要：滑らかなアフィン射の切断を通る成分は、整基底のある非空開部分上で開集合になる。
方針：生成成分の冪等元を主開に降ろし、剰余体上の表示を位相ファイバーへ移す。
規約：開集合は元の始域と基底のスペクトル上に取る。
使われ方：既約閉部分ごとの構成可能性判定。
-/
theorem exists_open_stratum_sectionComponentLocus_of_smooth
    {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] (s : B →ₐ[A] A) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let t := Spec.map (CommRingCat.ofHom s.toRingHom)
    ∃ (U : TopologicalSpace.Opens (Spec (.of A))) (W : TopologicalSpace.Opens (Spec (.of B))),
      (U : Set (Spec (.of A))).Nonempty ∧
        sectionComponentLocus f t ∩ f ⁻¹' (U : Set (Spec (.of A))) =
          (W : Set (Spec (.of B))) ∩ f ⁻¹' (U : Set (Spec (.of A))) := by
  obtain ⟨a, ha, e, r, hr, _, hSpread⟩ :=
    exists_generic_stratum_sectionComponent_eq_basicOpen (K := FractionRing A) s
  let S := Localization.Away a
  let : IsDomain S := Localization.Away.isDomain ha
  let D := S ⊗[A] B
  let f : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let t : Spec (.of A) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom s.toRingHom)
  let g : Spec (.of S) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A S))
  let i : Spec (.of D) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom)
  let f' : Spec (.of D) ⟶ Spec (.of S) := Spec.map (CommRingCat.ofHom (algebraMap S D))
  let v : D →ₐ[S] S := baseChangeSection s
  let t' : Spec (.of S) ⟶ Spec (.of D) := Spec.map (CommRingCat.ofHom v.toRingHom)
  have hPb : IsPullback i f' f g := isPullback_specTensor A B S
  have hg : IsOpenImmersion g := IsOpenImmersion.of_isLocalization a
  let : IsOpenImmersion i := MorphismProperty.of_isPullback hPb.flip hg
  have ht : t' ≫ f' = 𝟙 _ := spec_baseChangeSection_section s S
  have hComp : t' ≫ i = g ≫ t := spec_baseChangeSection_comm s S
  have hLocus := preimage_sectionComponentLocus_of_isPullback_of_isEmbedding
    hPb i.isOpenEmbedding.isEmbedding t t' ht hComp
  have hFiber (x : Spec (.of D)) (hx : f' x ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum S))) :
      x ∈ sectionComponentLocus f' t' ↔
        x ∈ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum D)) := by
    let p : PrimeSpectrum S := f' x
    have hp : algebraMap S p.asIdeal.ResidueField r ≠ 0 :=
      fun h => (PrimeSpectrum.mem_basicOpen r p).mp hx (Ideal.algebraMap_residueField_eq_zero.mp h)
    let k := PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : D →ₐ[S] p.asIdeal.ResidueField ⊗[S] D).toRingHom
    have hxRange : x ∈ Set.range k := by
      rw [range_comap_includeRight_residueField (B := D) p]
      exact Set.mem_singleton _
    obtain ⟨z, hz⟩ := hxRange
    have hMem : k z ∈ sectionComponentLocus f' t' ↔
        z ∈ (PrimeSpectrum.basicOpen (1 ⊗ₜ[S] e : p.asIdeal.ResidueField ⊗[S] D) : Set _) := by
      change z ∈ k ⁻¹' sectionComponentLocus f' t' ↔ _
      rw [preimage_sectionComponentLocus_spec_residueField v p, hSpread _ hp]
    have hBasic : z ∈ (PrimeSpectrum.basicOpen (1 ⊗ₜ[S] e :
        p.asIdeal.ResidueField ⊗[S] D) : Set _) ↔
        k z ∈ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum D)) := Iff.rfl
    exact (congrArg (fun w : PrimeSpectrum D => w ∈ sectionComponentLocus f' t' ↔
      w ∈ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum D))) hz).mp (hMem.trans hBasic)
  let U : TopologicalSpace.Opens (Spec (.of A)) :=
    ⟨g '' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum S)),
      g.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen r).isOpen⟩
  let W : TopologicalSpace.Opens (Spec (.of B)) :=
    ⟨i '' (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum D)),
      i.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen e).isOpen⟩
  refine ⟨U, W, ?_, ?_⟩
  · refine ⟨g (⊥ : PrimeSpectrum S), (⊥ : PrimeSpectrum S), ?_, rfl⟩
    exact (PrimeSpectrum.mem_basicOpen r ⊥).mpr hr
  · ext x
    change (x ∈ sectionComponentLocus f t ∧ f x ∈ U) ↔ (x ∈ W ∧ f x ∈ U)
    refine and_congr_left_iff.mpr fun hx => ?_
    obtain ⟨y, hy, hyx⟩ := hx
    obtain ⟨z, hzx, hzy⟩ := Scheme.exists_preimage_of_isPullback hPb x y hyx.symm
    change i z = x at hzx
    change f' z = y at hzy
    have hz : f' z ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum S)) := hzy.symm ▸ hy
    subst x
    change z ∈ i ⁻¹' sectionComponentLocus f t ↔
      i z ∈ i '' (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum D))
    rw [hLocus]
    exact (hFiber z hz).trans i.isOpenEmbedding.injective.mem_set_image.symm

end SerrePositivity.AlgebraicGeometry
