module

public import SerrePositivity.AlgebraicGeometry.GeometricFiberConnectedPoint
public import SerrePositivity.AlgebraicGeometry.MarkerTensorMaps
public import SerrePositivity.AlgebraicGeometry.SectionComponentMarkerDescent
public import SerrePositivity.AlgebraicGeometry.SmoothSectionComponentGeneralization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
概要：幾何学的に連結な指定ファイバーを、有限平坦な標識を使って開部分に広げる。
方針：標識上の切断の成分を自己ファイバー積上で比較し、基底を縮めて元の始域へ降下する。
規約：始域と基底はアフィンで、標識が指定ファイバーと交わるとする。
使われ方：滑らかな正規化先を幾何学的整なファイバーを持つ開部分に縮める。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped TensorProduct

private theorem mem_sectionComponentLocus_of_isConnected_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y)
    {x : X} (h : _root_.IsConnected (f ⁻¹' {f x})) :
    x ∈ sectionComponentLocus f s := by
  have hy : s (f x) ∈ f ⁻¹' {f x} := by
    have e := congrArg (fun g : Y ⟶ Y => g (f x)) hs
    simpa [Scheme.Hom.comp_apply] using e
  change x ∈ connectedComponentIn (f ⁻¹' {f x}) (s (f x))
  exact h.isPreconnected.subset_connectedComponentIn hy Set.Subset.rfl (Set.mem_singleton _)

/--
概要：滑らかなアフィン射と有限平坦な標識があり、指定ファイバーが幾何学的に連結なら、
基底を縮めて標識の切断を通る成分を、指定ファイバー全体を含む準コンパクト開に降下できる。
方針：自己ファイバー積の両側で切断の成分が一致する開近傍を取り、開写像による降下を使う。
規約：指定点の幾何学的連結性は、そこに写るすべての体への底変換について仮定する。
使われ方：Stacks 057I の滑らかなアフィンの場合。
-/
theorem exists_compact_open_of_smooth_finite_flat_marker
    {A B T : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [CommRing T]
    [Algebra A B] [Algebra A T] [Algebra.Smooth A B] [Module.Finite A T] [Module.Flat A T]
    (σ : B →ₐ[A] T) (a : PrimeSpectrum A)
    (hConn : ∀ (K : Type u) [Field K] [Algebra A K],
      (⊥ : PrimeSpectrum K).comap (algebraMap A K) = a →
        ConnectedSpace (PrimeSpectrum (K ⊗[A] B)))
    (hMark : ∃ z : PrimeSpectrum T, z.comap (algebraMap A T) = a) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let i := Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[A] T ⊗[A] B).toRingHom)
    let fT := Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[A] B)))
    let t := Spec.map (CommRingCat.ofHom (AlgHom.liftEquiv A T B T σ).toRingHom)
    ∃ (U : (Spec (.of A)).Opens) (V : (Spec (.of B)).Opens), IsAffineOpen U ∧ a ∈ U ∧
      IsCompact (V : Set (Spec (.of B))) ∧ V ≤ f ⁻¹ᵁ U ∧
      f ⁻¹' ({a} : Set (Spec (.of A))) ⊆ V ∧
      i ⁻¹' (V : Set (Spec (.of B))) =
        sectionComponentLocus fT t ∩ (i ≫ f) ⁻¹' (U : Set (Spec (.of A))) := by
  let E := T ⊗[A] B
  let P := T ⊗[A] T
  let D := P ⊗[A] B
  let f : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g : Spec (.of T) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A T))
  let q : Spec (.of P) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A P))
  let i : Spec (.of E) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[A] E).toRingHom)
  let fT : Spec (.of E) ⟶ Spec (.of T) := Spec.map (CommRingCat.ofHom (algebraMap T E))
  let fP : Spec (.of D) ⟶ Spec (.of P) := Spec.map (CommRingCat.ofHom (algebraMap P D))
  let τ : E →ₐ[T] T := AlgHom.liftEquiv A T B T σ
  let t : Spec (.of T) ⟶ Spec (.of E) := Spec.map (CommRingCat.ofHom τ.toRingHom)
  let u (k : T →ₐ[A] P) := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.map k (AlgHom.id A B)).toRingHom)
  let v (k : T →ₐ[A] P) : D →ₐ[P] P := AlgHom.liftEquiv A P B P (k.comp σ)
  let s (k : T →ₐ[A] P) := Spec.map (CommRingCat.ofHom (v k).toRingHom)
  let l : T →ₐ[A] P := Algebra.TensorProduct.includeLeft
  let r : T →ₐ[A] P := Algebra.TensorProduct.includeRight
  have hE : IsPullback i fT f g := isPullback_specTensor A B T
  have hSelf : IsPullback (u l) (u r) i i := isPullback_specTensor_markerSelf A B T
  let : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing A T
  let : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing T E
  let : NoetherianSpace (Spec (.of E)) := inferInstanceAs (NoetherianSpace (PrimeSpectrum E))
  let W : (Spec (.of E)).Opens := ⟨sectionComponentLocus fT t,
    isOpen_sectionComponentLocus_of_smooth τ⟩
  let : Flat g := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : LocallyOfFinitePresentation g :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr
        (Algebra.FinitePresentation.of_finiteType.mp (inferInstance : Algebra.FiniteType A T)))
  let : UniversallyOpen i := MorphismProperty.of_isPullback hE.flip
    (inferInstance : UniversallyOpen g)
  let : IsFinite q := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hC (k : T →ₐ[A] P) : u k ⁻¹' (W : Set (Spec (.of E))) =
      sectionComponentLocus fP (s k) := preimage_sectionComponentLocus_marker_map σ k
  have hs (k : T →ₐ[A] P) : s k ≫ fP = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (v k).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap P D)) = _
    rw [← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext (v k).commutes))
  let j : Spec (.of D) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom)
  have hji : u l ≫ i = j := by
    change Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map l (AlgHom.id A B)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] E).toRingHom) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom)
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change (Algebra.TensorProduct.map l (AlgHom.id A B)) (1 ⊗ₜ[A] b) = 1 ⊗ₜ[A] b
    simp
  have hbase : u l ≫ i ≫ f = fP ≫ q := by
    rw [← Category.assoc, hji]
    exact (isPullback_specTensor A B P).w
  have hSame (y : Spec (.of P)) (hy : q y = a) : s l y ∈ sectionComponentLocus fP (s r) := by
    apply mem_sectionComponentLocus_of_isConnected_fiber fP (s r) (hs r)
    have hy' : fP (s l y) = y := by
      have e := congrArg (fun k : Spec (.of P) ⟶ Spec (.of P) => k y) (hs l)
      simpa [Scheme.Hom.comp_apply] using e
    rw [hy']
    exact isConnected_specTensor_fiber_of_geometricFiberAt a hConn y hy
  obtain ⟨U, V, hU, ha, hc, hVU, heq⟩ :=
    exists_open_sectionComponentMarker_descent hSelf i.isOpenMap f fP q q.isClosedMap hbase
      W (s l) (s r) (hs l) (hC l) (hC r) a hSame
  refine ⟨U, V, hU, ha, hc, hVU, ?_, heq⟩
  intro x hx
  obtain ⟨y, hy⟩ := hMark
  have hx' : f x = a := hx
  have hy' : g y = a := hy
  obtain ⟨z, hzx, hzy⟩ := Scheme.exists_preimage_of_isPullback hE x y (hx'.trans hy'.symm)
  change i z = x at hzx
  change fT z = y at hzy
  have ht : t ≫ fT = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap T E)) = _
    rw [← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext τ.commutes))
  have hzW : z ∈ W := by
    apply mem_sectionComponentLocus_of_isConnected_fiber fT t ht
    rw [hzy]
    exact isConnected_specTensor_fiber_of_geometricFiberAt a hConn y hy
  have hzU : (i ≫ f) z ∈ U := by simpa [Scheme.Hom.comp_apply, hzx, hx'] using ha
  have hzV := (Set.ext_iff.mp heq z).mpr ⟨hzW, hzU⟩
  change i z ∈ V at hzV
  rwa [hzx] at hzV

end SerrePositivity.AlgebraicGeometry
