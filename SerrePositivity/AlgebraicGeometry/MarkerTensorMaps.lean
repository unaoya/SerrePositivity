module

public import SerrePositivity.AlgebraicGeometry.SectionComponentIteratedBaseChange

/-!
概要：アフィンな標識の自己ファイバー積と、その上の二つの底変換をテンソル積で表す。
方針：基底変更の合成の同型を使い、二つの引き戻しの四角形を貼り合わせる。
規約：標識の環をテンソル積の左に置く。
使われ方：滑らかな族で有限標識の二つの切断の成分を比較する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

/--
概要：二段階の底変換を一段階にしたときの始域への環写像は、左因子の写像と右因子の恒等写像のテンソル。
方針：単純テンソルで、標準同型の評価とテンソル積の写像を比較する。
規約：最初の基底変更先を左因子とする。
使われ方：自己ファイバー積の二つの射を同じテンソル積表示で扱う。
-/
theorem cancelBaseChange_comp_includeRight_eq_map
    {A B T V : Type u} [CommRing A] [CommRing B] [CommRing T] [CommRing V]
    [Algebra A B] [Algebra A T] [Algebra A V] [Algebra T V] [IsScalarTower A T V] :
    ((Algebra.TensorProduct.cancelBaseChange A T V V B).toRingHom.comp
      (Algebra.TensorProduct.includeRight : T ⊗[A] B →ₐ[T] V ⊗[T] (T ⊗[A] B)).toRingHom) =
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A T V) (AlgHom.id A B)).toRingHom := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul t b =>
    change (Algebra.TensorProduct.cancelBaseChange A T V V B) (1 ⊗ₜ[T] (t ⊗ₜ[A] b)) =
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A T V) (AlgHom.id A B)) (t ⊗ₜ[A] b)
    rw [Algebra.TensorProduct.map_tmul]
    have h := Algebra.TensorProduct.cancelBaseChange_tmul A T V V B (1 : V) t b
    exact h.trans (by simp [Algebra.smul_def])
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/--
概要：標識から得た切断を二段階で底変換しても、合成した標識から得る切断に一致する。
方針：一段階のテンソル積の単純テンソル上で、切断の評価の式を使う。
規約：標識は基底上の代数準同型で表す。
使われ方：同じ始域上の二つの切断を自己ファイバー積の各射から作る。
-/
theorem baseChangeSection_liftEquiv_comp_cancelBaseChange_symm
    {A B T V : Type u} [CommRing A] [CommRing B] [CommRing T] [CommRing V]
    [Algebra A B] [Algebra A T] [Algebra A V] [Algebra T V] [IsScalarTower A T V]
    (s : B →ₐ[A] T) :
    (baseChangeSection (AlgHom.liftEquiv A T B T s) :
        V ⊗[T] (T ⊗[A] B) →ₐ[V] V).comp
        (Algebra.TensorProduct.cancelBaseChange A T V V B).symm.toAlgHom =
      AlgHom.liftEquiv A V B V ((IsScalarTower.toAlgHom A T V).comp s) := by
  apply Algebra.TensorProduct.ext'
  intro v b
  change baseChangeSection (AlgHom.liftEquiv A T B T s)
      ((Algebra.TensorProduct.cancelBaseChange A T V V B).symm (v ⊗ₜ[A] b)) = _
  have h := Algebra.TensorProduct.cancelBaseChange_symm_tmul A T V V B v b
  rw [h, baseChangeSection_tmul]
  change v * algebraMap T V ((1 : T) • s b) = v • algebraMap T V (s b)
  rw [one_smul, smul_eq_mul]

/--
概要：アフィン底変換の二段目は、基底の代数準同型と始域の恒等写像のテンソルで表せる。
方針：基底変更の標準同型と、テンソル積の引き戻しを使う。
規約：二段目の基底変更は代数準同型として指定する。
使われ方：有限標識の二つの射に沿う引き戻しの比較。
-/
theorem isPullback_specTensor_map
    {A B T V : Type u} [CommRing A] [CommRing B] [CommRing T] [CommRing V]
    [Algebra A B] [Algebra A T] [Algebra A V] (k : T →ₐ[A] V) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map k (AlgHom.id A B)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap V (V ⊗[A] B))))
      (Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[A] B))))
      (Spec.map (CommRingCat.ofHom k.toRingHom)) := by
  let : Algebra T V := k.toRingHom.toAlgebra
  let : IsScalarTower A T V := IsScalarTower.of_algebraMap_eq fun a => (k.commutes a).symm
  have hk : IsScalarTower.toAlgHom A T V = k := AlgHom.ext fun _ => rfl
  have h := isPullback_specTensor_cancel (A := A) (B := B) (T := T) (V := V)
  dsimp only at h
  rw [cancelBaseChange_comp_includeRight_eq_map, hk] at h
  exact h

/--
概要：標識から作る切断を通る成分の族は、標識の任意の底変換と可換。
方針：二段目のテンソル積を一段目とまとめ、合成した標識の切断と比較する。
規約：標識と基底変更は、もとの基底上の代数準同型で与える。
使われ方：有限標識の自己ファイバー積上の二つの成分の族。
-/
theorem preimage_sectionComponentLocus_marker_map
    {A B T V : Type u} [CommRing A] [CommRing B] [CommRing T] [CommRing V]
    [Algebra A B] [Algebra A T] [Algebra A V] [Algebra.FiniteType A B]
    (σ : B →ₐ[A] T) (k : T →ₐ[A] V) :
    PrimeSpectrum.comap (Algebra.TensorProduct.map k (AlgHom.id A B)).toRingHom ⁻¹'
        sectionComponentLocus (Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[A] B))))
          (Spec.map (CommRingCat.ofHom (AlgHom.liftEquiv A T B T σ).toRingHom)) =
      sectionComponentLocus (Spec.map (CommRingCat.ofHom (algebraMap V (V ⊗[A] B))))
        (Spec.map (CommRingCat.ofHom (AlgHom.liftEquiv A V B V (k.comp σ)).toRingHom)) := by
  let : Algebra T V := k.toRingHom.toAlgebra
  let : IsScalarTower A T V := IsScalarTower.of_algebraMap_eq fun a => (k.commutes a).symm
  have hk : IsScalarTower.toAlgHom A T V = k := AlgHom.ext fun _ => rfl
  have h := preimage_sectionComponentLocus_specTensor_cancel (V := V) (AlgHom.liftEquiv A T B T σ)
  dsimp only at h
  rw [cancelBaseChange_comp_includeRight_eq_map,
    baseChangeSection_liftEquiv_comp_cancelBaseChange_symm, hk] at h
  exact h

/--
概要：底変換の始域の自己ファイバー積は、標識の環のテンソル積で底変換したアフィンスキーム。
方針：標識の二つの射に沿うアフィンの引き戻しを貼り合わせる。
規約：自己ファイバー積の二つの射は、標識の左と右の包含から作る。
使われ方：標識上の開部分の降下条件を、二つの切断の比較に置き換える。
-/
theorem isPullback_specTensor_markerSelf
    (A B T : Type u) [CommRing A] [CommRing B] [CommRing T] [Algebra A B] [Algebra A T] :
    let V := T ⊗[A] T
    let i := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      B →ₐ[A] T ⊗[A] B).toRingHom)
    let u (k : T →ₐ[A] V) :=
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map k (AlgHom.id A B)).toRingHom)
    IsPullback
      (u Algebra.TensorProduct.includeLeft) (u Algebra.TensorProduct.includeRight) i i := by
  let V := T ⊗[A] T
  let E := T ⊗[A] B
  let D := V ⊗[A] B
  let i : Spec (.of E) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] E).toRingHom)
  let f : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let fT : Spec (.of E) ⟶ Spec (.of T) := Spec.map (CommRingCat.ofHom (algebraMap T E))
  let g : Spec (.of T) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A T))
  let fV : Spec (.of D) ⟶ Spec (.of V) := Spec.map (CommRingCat.ofHom (algebraMap V D))
  let π (k : T →ₐ[A] V) := Spec.map (CommRingCat.ofHom k.toRingHom)
  let u (k : T →ₐ[A] V) :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map k (AlgHom.id A B)).toRingHom)
  let l : T →ₐ[A] V := Algebra.TensorProduct.includeLeft
  let r : T →ₐ[A] V := Algebra.TensorProduct.includeRight
  have hV : IsPullback (π l) (π r) g g := (isPullback_specTensor A T T).flip
  have hE : IsPullback i fT f g := isPullback_specTensor A B T
  have hD (k : T →ₐ[A] V) : IsPullback (u k) fV fT (π k) :=
    isPullback_specTensor_map k
  have hOuter := (hD l).paste_vert hV
  rw [← (hD r).w, ← hE.w] at hOuter
  change IsPullback (u l) (u r) i i
  refine IsPullback.of_bot hOuter ?_ hE
  change Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map l (AlgHom.id A B)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] E).toRingHom) =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map r (AlgHom.id A B)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] E).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  change (Algebra.TensorProduct.map l (AlgHom.id A B)) (1 ⊗ₜ[A] b) =
    (Algebra.TensorProduct.map r (AlgHom.id A B)) (1 ⊗ₜ[A] b)
  simp

end SerrePositivity.AlgebraicGeometry
