module

public import SerrePositivity.AlgebraicGeometry.SectionComponentLocus
public import SerrePositivity.AlgebraicGeometry.SmoothSectionGenericStratum
public import Mathlib.AlgebraicGeometry.Fiber

/-!
概要：アフィン射の切断を通る成分を、体とテンソルした代数のスペクトル上で計算する。
方針：テンソル積の引き戻しで切断を比較し、剰余体による底変換には埋め込みの補題を使う。
規約：基底の体はその点の剰余体を使う。
使われ方：冪等元によるファイバー上の成分の表示を始域の開部分に移す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

/--
概要：底変換した切断の評価を単純テンソルで計算する。
方針：テンソル積の普遍性で定めた写像の式を展開する。
規約：基底変更先の元をテンソル積の左に置く。
使われ方：体拡大と剰余体上での切断の比較。
-/
theorem baseChangeSection_tmul
    {A B F : Type u} [CommRing A] [CommRing B] [CommRing F]
    [Algebra A B] [Algebra A F] (s : B →ₐ[A] A) (y : F) (b : B) :
    baseChangeSection s (y ⊗ₜ[A] b) = y * algebraMap A F (s b) := by
  change y • (algebraMap A F (s b)) = _
  rw [smul_eq_mul]

/--
概要：切断のファイバー上の点は、テンソル積の左右の順序を交換しても同じ。
方針：単純テンソルの評価の可換性から環準同型を比較する。
規約：左に体を置く場合は底変換した切断の核で表す。
使われ方：剰余体上の点の比較。
-/
theorem sectionPointInTensor_comm
    {A B F : Type u} [CommRing A] [CommRing B] [Field F]
    [Algebra A B] [Algebra A F] (s : B →ₐ[A] A) :
    (⊥ : PrimeSpectrum F).comap (baseChangeSection s : F ⊗[A] B →ₐ[F] F).toRingHom =
      (sectionPointInTensor F s).comap (Algebra.TensorProduct.comm A F B).toRingHom := by
  have hEval : (baseChangeSection s : F ⊗[A] B →ₐ[F] F).toRingHom =
      (sectionFiberEval (L := F) s).toRingHom.comp
        (Algebra.TensorProduct.comm A F B).toRingHom := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul y b =>
      change baseChangeSection s (y ⊗ₜ[A] b) = sectionFiberEval s (b ⊗ₜ[A] y)
      rw [baseChangeSection_tmul]
      change y * algebraMap A F (s b) = s b • y
      rw [Algebra.smul_def, mul_comm]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hEval]
  rfl

/--
概要：テンソル積の二つの標準射はアフィンスキームの引き戻しを与える。
方針：可換環の押し出しを Spec で引き戻しに移す。
規約：基底変更先の代数をテンソル積の左に置く。
使われ方：アフィン射のファイバーと基底変更。
-/
theorem isPullback_specTensor
    (A B F : Type u) [CommRing A] [CommRing B] [CommRing F] [Algebra A B] [Algebra A F] :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[A] F ⊗[A] B).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap F (F ⊗[A] B))))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A F))) := by
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A F B)).flip

/--
概要：底変換した環準同型は底変換後の射の切断を与える。
方針：テンソル積の左因子で代数準同型が恒等になることを使う。
規約：基底変更先をテンソル積の左に置く。
使われ方：底変換後の切断を通るファイバー成分。
-/
theorem spec_baseChangeSection_section
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (s : B →ₐ[A] A) (F : Type u) [CommRing F] [Algebra A F] :
    Spec.map (CommRingCat.ofHom (baseChangeSection s : F ⊗[A] B →ₐ[F] F).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap F (F ⊗[A] B))) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (baseChangeSection s : F ⊗[A] B →ₐ[F] F).commutes

/--
概要：底変換した切断を始域へ戻すと、基底変更射と元の切断の合成になる。
方針：底変換した評価をテンソル積の右因子で計算する。
規約：基底変更先をテンソル積の左に置く。
使われ方：底変換の前後で切断を通るファイバー成分を比較する。
-/
theorem spec_baseChangeSection_comm
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (s : B →ₐ[A] A) (F : Type u) [CommRing F] [Algebra A F] :
    Spec.map (CommRingCat.ofHom (baseChangeSection s : F ⊗[A] B →ₐ[F] F).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[A] F ⊗[A] B).toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap A F)) ≫ Spec.map (CommRingCat.ofHom s.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change baseChangeSection s ((1 : F) ⊗ₜ[A] x) = algebraMap A F (s x)
  rw [baseChangeSection_tmul, one_mul]

/--
概要：アフィン射の切断を通るファイバー成分は、剰余体とテンソルした環で切断を通る連結成分になる。
方針：剰余体への写像の引き戻しで成分を比較し、剰余体のスペクトルが一点であることを使う。
規約：ファイバーから始域への写像は右因子の包含に対応する。
使われ方：アフィン射の切断を通る成分の構成可能性。
-/
theorem preimage_sectionComponentLocus_spec_residueField
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (s : B →ₐ[A] A)
    (p : PrimeSpectrum A) :
    PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : B →ₐ[A] p.asIdeal.ResidueField ⊗[A] B).toRingHom ⁻¹'
      sectionComponentLocus (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom s.toRingHom)) =
      connectedComponent ((sectionPointInTensor p.asIdeal.ResidueField s).comap
        (Algebra.TensorProduct.comm A p.asIdeal.ResidueField B).toRingHom) := by
  let F := p.asIdeal.ResidueField
  let D := F ⊗[A] B
  let i : Spec (.of D) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom)
  let f' : Spec (.of D) ⟶ Spec (.of F) := Spec.map (CommRingCat.ofHom (algebraMap F D))
  let f : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g : Spec (.of F) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A F))
  let v : D →ₐ[F] F := baseChangeSection s
  let t : Spec (.of F) ⟶ Spec (.of D) := Spec.map (CommRingCat.ofHom v.toRingHom)
  let s' : Spec (.of A) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom s.toRingHom)
  have hPb : IsPullback i f' f g := isPullback_specTensor A B F
  let j := Spec.map (Scheme.Spec.residueFieldIso (.of A) p).inv
  have hj : j ≫ g = (Spec (.of A)).fromSpecResidueField p :=
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of A) p
  let : IsIso j := inferInstanceAs
    (IsIso (Spec.map (Scheme.Spec.residueFieldIso (.of A) p).inv))
  have hPre : IsPreimmersion g := by
    have e : g = inv j ≫ (Spec (.of A)).fromSpecResidueField p := by
      rw [← hj, IsIso.inv_hom_id_assoc]
    rw [e]
    let : IsIso (inv j) := inferInstance
    let : IsOpenImmersion (inv j) := IsOpenImmersion.of_isIso (g := inv j)
    let : IsPreimmersion ((Spec (.of A)).fromSpecResidueField p) :=
      Scheme.instIsPreimmersionFromSpecResidueField (X := Spec (.of A)) p
    exact IsPreimmersion.comp _ _
  have hi : IsPreimmersion i := MorphismProperty.of_isPullback hPb.flip hPre
  have ht : t ≫ f' = 𝟙 _ := spec_baseChangeSection_section s F
  have hComp : t ≫ i = g ≫ s' := spec_baseChangeSection_comm s F
  change i ⁻¹' sectionComponentLocus f s' = _
  rw [preimage_sectionComponentLocus_of_isPullback_of_isEmbedding hPb i.isEmbedding s' t ht hComp]
  ext x
  change x ∈ connectedComponentIn (f' ⁻¹' {f' x}) (t (f' x)) ↔ _
  have hp : f' x = (⊥ : PrimeSpectrum F) := Subsingleton.elim _ _
  have hUniv : f' ⁻¹' {f' x} = Set.univ := by
    ext y
    exact ⟨fun _ => Set.mem_univ _, fun _ => Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)⟩
  rw [hUniv, connectedComponentIn_univ, hp]
  change x ∈ connectedComponent ((⊥ : PrimeSpectrum F).comap v.toRingHom) ↔ _
  rw [sectionPointInTensor_comm (F := F) s]
  rfl

/--
概要：剰余体とテンソルした代数のスペクトルの像は、その点の位相ファイバー。
方針：アフィンの引き戻しを使い、剰余体のスペクトルの像を指定点と同定する。
規約：剰余体をテンソル積の左に置く。
使われ方：ファイバー内の成分の表示を始域の部分集合へ移す。
-/
theorem range_comap_includeRight_residueField
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (p : PrimeSpectrum A) :
    Set.range (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight :
        B →ₐ[A] p.asIdeal.ResidueField ⊗[A] B).toRingHom) =
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p} := by
  let F := p.asIdeal.ResidueField
  let g : Spec (.of F) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A F))
  let j := Spec.map (Scheme.Spec.residueFieldIso (.of A) p).inv
  have hj : j ≫ g = (Spec (.of A)).fromSpecResidueField p :=
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of A) p
  let : IsIso j := inferInstanceAs
    (IsIso (Spec.map (Scheme.Spec.residueFieldIso (.of A) p).inv))
  have hSurj : Function.Surjective j := j.homeomorph.surjective
  have hRange : Set.range g = ({p} : Set (Spec (.of A))) := by
    calc
      Set.range g = Set.range (g ∘ j) := by rw [Set.range_comp, hSurj.range_eq, Set.image_univ]
      _ = Set.range ((Spec (.of A)).fromSpecResidueField p) := by
        change Set.range (⇑(j ≫ g)) = _
        rw [hj]
      _ = _ := Scheme.range_fromSpecResidueField (X := Spec (.of A)) p
  have hImage := Scheme.image_preimage_eq_of_isPullback (isPullback_specTensor A B F).flip
    (Set.univ : Set (Spec (.of F)))
  let D := F ⊗[A] B
  let i : Spec (.of D) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom)
  let f' : Spec (.of D) ⟶ Spec (.of F) := Spec.map (CommRingCat.ofHom (algebraMap F D))
  let f : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  change i '' (f' ⁻¹' (Set.univ : Set (Spec (.of F)))) =
    f ⁻¹' (g '' (Set.univ : Set (Spec (.of F)))) at hImage
  change Set.range i = f ⁻¹' ({p} : Set (Spec (.of A)))
  simpa only [Set.preimage_univ, Set.image_univ, hRange] using hImage

end SerrePositivity.AlgebraicGeometry
