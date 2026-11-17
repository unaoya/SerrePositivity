module

public import SerrePositivity.AlgebraicGeometry.ProperSurjectivePerfectCechUniversalDescent
public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalAffineRefinement
public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalFppfComposite
public import SerrePositivity.AlgebraicGeometry.AffineBaseVCoverRefinement
public import SerrePositivity.AlgebraicGeometry.RelativeFppfAffineRefinement
public import SerrePositivity.AlgebraicGeometry.SpecScalarPerfectTupleTotal
public import SerrePositivity.AlgebraicGeometry.NilBaseChangePerfectCech

/-!
概要：Noether基底上の有限表示なaffine v被覆のFrobenius係数のČech完全性。
方針：Rydhのfppf–proper細分、固有全射の判定、アフィン細分の消去を合成する。
規約：元の環準同型の増大conerveへ戻し、同じ最終の型を保つ。
使われ方：filtered被覆模型の各有限段（承認済み計画I13）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- Noether基底上の元の有限表示v被覆の同じFrobenius係数はČech完全。 -/
theorem noetherianAffineVCover_frobeniusCechExact
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (f : R →+* S) (hfp : f.FinitePresentation) (hv : IsAffineVCover f)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients (Arrow.mk (CommRingCat.ofHom f)) p hp hR) := by
  let g := Spec.map (CommRingCat.ofHom f)
  haveI : LocallyOfFinitePresentation g := (LocallyOfFinitePresentation.SpecMap_iff _).mpr hfp
  have hg : IsSchemeVCover g := (isSchemeVCover_specMap_iff f).mpr hv
  obtain ⟨T, W, r, q, k, hr, hrs, hrfp, hrqc, hq, hqs, hqfp, hqqc, hcomm⟩ :=
    exists_fppf_proper_refinement_vCover_affineBase g hg
  haveI : IsProper r := hr
  haveI : Surjective r := hrs
  haveI : LocallyOfFinitePresentation r := hrfp
  haveI : QuasiCompact r := hrqc
  haveI : Flat q := hq
  haveI : Surjective q := hqs
  haveI : LocallyOfFinitePresentation q := hqfp
  haveI : QuasiCompact q := hqqc
  haveI : T.IsSeparated := ⟨by rw [← terminal.comp_from r]; infer_instance⟩
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace r
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace q
  obtain ⟨A, hA, a, haFlat, haSurj, haFp, haAffine⟩ :=
    exists_affine_flatSurjective_refinement q
  haveI : IsAffine A := hA
  let qA := a ≫ q
  haveI : Flat qA := haFlat
  haveI : Surjective qA := haSurj
  haveI : LocallyOfFinitePresentation qA := haFp
  haveI : IsAffineHom qA := haAffine
  have htotal := perfectCechUniversalDescent_affine_fppf_comp qA r p hp
    (properSurjective_perfectCechUniversalDescent r p hp)
  have hk : (a ≫ k) ≫ g = qA ≫ r := by rw [Category.assoc, hcomm, ← Category.assoc]
  haveI : IsAffineHom ((a ≫ k) ≫ g) := inferInstance
  haveI : LocallyOfFinitePresentation ((a ≫ k) ≫ g) := by rw [hk]; infer_instance
  have hd : PerfectCechUniversalDescent p hp g := by
    apply perfectCechUniversalDescent_of_affine_refinement p hp g (a ≫ k)
    rw [hk]
    exact htotal
  let U : Unit → (Spec (CommRingCat.of S)).Opens := fun _ ↦ ⊤
  have hU (i : Unit) : IsAffineOpen (U i) := isAffineOpen_top _
  have hcU : (⨆ i, U i) = ⊤ := by simp [U]
  let F : Arrow.mk (pullback.snd g (𝟙 (Spec (CommRingCat.of R)))) ⟶ Arrow.mk g :=
    Arrow.homMk (pullback.fst g (𝟙 _)) (𝟙 _) pullback.condition
  haveI : IsIso F.left := by change IsIso (pullback.fst g (𝟙 _)); infer_instance
  haveI : IsIso F.right := by change IsIso (𝟙 (Spec (CommRingCat.of R))); infer_instance
  have H : IsPullback F.left (pullback.snd g (𝟙 (Spec (CommRingCat.of R)))) g F.right :=
    IsPullback.of_hasPullback g (𝟙 _)
  have hbase : F.right = Spec.map (CommRingCat.ofHom (RingHom.id R)) := (Spec.map_id _).symm
  have hPC := (nilBaseChange_tupleTotal_acyclic_iff
    (pullback.snd g (𝟙 (Spec (CommRingCat.of R)))) g F H (RingHom.id R) hbase
      p hp hR hR U hU).mpr
        (hd R hR (𝟙 _) Unit (fun i ↦ F.left ⁻¹ᵁ U i)
          (fun i ↦ (hU i).preimage F.left) (F.left.iSup_preimage_eq_top hcU))
  exact (ringFrobeniusCech_exact_iff_spec_tuple_total_acyclic f p hp hR U hU hcU).mpr hPC

end SerrePositivity.AlgebraicGeometry
