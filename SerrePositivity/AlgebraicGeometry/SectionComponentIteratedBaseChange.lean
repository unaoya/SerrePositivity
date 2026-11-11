module

public import SerrePositivity.AlgebraicGeometry.SectionComponentTensorBaseChange

/-!
概要：アフィン射の切断を通る成分を、二段階の底変換を一段階にした表示で比較する。
方針：テンソル積の標準同型を、切断と両立する引き戻しとして使う。
規約：二段階の底変換先は、指定した代数の塔で与える。
使われ方：有限局所自由な標識の自己ファイバー積で二つの切断を同じ始域に置く。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

/--
概要：アフィン射を二度底変換する引き戻しは、二重テンソル積を一段階にした環で表せる。
方針：通常のテンソル積の引き戻しを、底変換の標準同型で移す。
規約：最初の基底変更先と次の基底変更先の間には代数の塔を取る。
使われ方：有限標識を引き戻した二つの図式を貼り合わせる。
-/
theorem isPullback_specTensor_cancel
    {A B T V : Type u} [CommRing A] [CommRing B] [CommRing T] [CommRing V]
    [Algebra A B] [Algebra A T] [Algebra A V] [Algebra T V] [IsScalarTower A T V] :
    let e := Algebra.TensorProduct.cancelBaseChange A T V V B
    let j := e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : T ⊗[A] B →ₐ[T] V ⊗[T] (T ⊗[A] B)).toRingHom
    IsPullback (Spec.map (CommRingCat.ofHom j))
      (Spec.map (CommRingCat.ofHom (algebraMap V (V ⊗[A] B))))
      (Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[A] B))))
      (Spec.map (CommRingCat.ofHom (algebraMap T V))) := by
  let E := T ⊗[A] B
  let P := V ⊗[T] E
  let D := V ⊗[A] B
  let e : P ≃ₐ[V] D := Algebra.TensorProduct.cancelBaseChange A T V V B
  let i : Spec (.of D) ⟶ Spec (.of P) := Spec.map (CommRingCat.ofHom e.toRingHom)
  let : IsIso i := inferInstanceAs (IsIso (Spec.map e.toRingEquiv.toCommRingCatIso.hom))
  refine (isPullback_specTensor T E V).of_iso' (asIso i) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp)
  · simp only [asIso_hom, Iso.refl_hom, Category.comp_id]
    exact (Spec.map_comp _ _).symm
  · simp only [asIso_hom, Iso.refl_hom, Category.comp_id]
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap V P)) = Spec.map (CommRingCat.ofHom (algebraMap V D))
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext e.commutes))

/--
概要：底変換で得たアフィン射に切断があるとき、さらに底変換した成分は、
二段階のテンソル積を一段階にした表示でも、もとの成分の逆像になる。
方針：通常の底変換の比較と、テンソル積を一段階にする同型による比較を合成する。
規約：有限型性は最初のアフィン射に仮定する。
使われ方：Stacks 057I の有限標識の二つの底変換。
-/
theorem preimage_sectionComponentLocus_specTensor_cancel
    {A B T V : Type u} [CommRing A] [CommRing B] [CommRing T] [CommRing V]
    [Algebra A B] [Algebra A T] [Algebra A V] [Algebra T V] [IsScalarTower A T V]
    [Algebra.FiniteType A B] (s : T ⊗[A] B →ₐ[T] T) :
    let e := Algebra.TensorProduct.cancelBaseChange A T V V B
    let j := e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : T ⊗[A] B →ₐ[T] V ⊗[T] (T ⊗[A] B)).toRingHom
    let v := (baseChangeSection s : V ⊗[T] (T ⊗[A] B) →ₐ[V] V).comp e.symm.toAlgHom
    PrimeSpectrum.comap j ⁻¹' sectionComponentLocus
        (Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[A] B))))
        (Spec.map (CommRingCat.ofHom s.toRingHom)) =
      sectionComponentLocus (Spec.map (CommRingCat.ofHom (algebraMap V (V ⊗[A] B))))
        (Spec.map (CommRingCat.ofHom v.toRingHom)) := by
  let E := T ⊗[A] B
  let P := V ⊗[T] E
  let D := V ⊗[A] B
  let e : P ≃ₐ[V] D := Algebra.TensorProduct.cancelBaseChange A T V V B
  let u : P →ₐ[V] V := baseChangeSection s
  let v : D →ₐ[V] V := u.comp e.symm.toAlgHom
  let i : Spec (.of D) ⟶ Spec (.of P) := Spec.map (CommRingCat.ofHom e.toRingHom)
  let p : Spec (.of P) ⟶ Spec (.of V) := Spec.map (CommRingCat.ofHom (algebraMap V P))
  let d : Spec (.of D) ⟶ Spec (.of V) := Spec.map (CommRingCat.ofHom (algebraMap V D))
  let tu : Spec (.of V) ⟶ Spec (.of P) := Spec.map (CommRingCat.ofHom u.toRingHom)
  let tv : Spec (.of V) ⟶ Spec (.of D) := Spec.map (CommRingCat.ofHom v.toRingHom)
  let : IsIso i := inferInstanceAs (IsIso (Spec.map e.toRingEquiv.toCommRingCatIso.hom))
  have hip : i ≫ p = d ≫ 𝟙 _ := by
    rw [Category.comp_id]
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap V P)) = Spec.map (CommRingCat.ofHom (algebraMap V D))
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext e.commutes))
  have hPb : IsPullback i d p (𝟙 _) := IsPullback.of_horiz_isIso ⟨hip⟩
  have htv : tv ≫ d = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom v.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap V D)) = _
    rw [← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext v.commutes))
  have htu : tv ≫ i = 𝟙 _ ≫ tu := by
    rw [Category.id_comp]
    change Spec.map (CommRingCat.ofHom v.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) =
      Spec.map (CommRingCat.ofHom u.toRingHom)
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext fun z => congrArg u (e.symm_apply_apply z)
  let : IsOpenImmersion i := IsOpenImmersion.of_isIso (g := i)
  have hIso := preimage_sectionComponentLocus_of_isPullback_of_isEmbedding
    hPb i.isOpenEmbedding.isEmbedding tu tv htv htu
  let j : E →ₐ[T] P := Algebra.TensorProduct.includeRight
  let C : Set (PrimeSpectrum E) := sectionComponentLocus
    (Spec.map (CommRingCat.ofHom (algebraMap T E))) (Spec.map (CommRingCat.ofHom s.toRingHom))
  have hBase := preimage_sectionComponentLocus_specTensor s V
  change PrimeSpectrum.comap j.toRingHom ⁻¹' C = sectionComponentLocus p tu at hBase
  change PrimeSpectrum.comap (e.toRingHom.comp j.toRingHom) ⁻¹' C = sectionComponentLocus d tv
  rw [PrimeSpectrum.comap_comp, Set.preimage_comp, hBase]
  exact hIso

end SerrePositivity.AlgebraicGeometry
