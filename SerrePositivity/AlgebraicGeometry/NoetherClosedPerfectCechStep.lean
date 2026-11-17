module

public import SerrePositivity.AlgebraicGeometry.NoetherClosedCenterInput
public import SerrePositivity.AlgebraicGeometry.BlowupPerfectCechUniversalDescent
public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalAffineRefinement
public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalFppfComposite
public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalTargetIso
public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalNilReflection
public import SerrePositivity.AlgebraicGeometry.SchemeNilradicalReduction
public import SerrePositivity.AlgebraicGeometry.RelativeFppfAffineRefinement

/-!
概要：固有全射の完全構造層の降下性のNoether閉像帰納の一段。
方針：被約化し、元の平坦化の許容中心で帰納し、相対fppfの細分を消去する。
規約：元の固有全射の滑らかさは仮定せず、中心像だけを真に小さくする。
使われ方：Noetherアフィン基底上の固有全射（承認済み計画I10）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false

/-- 許容中心の真の閉像での帰納から、元の閉像上の固有全射のČech降下を得る。 -/
theorem noetherClosedPerfectCechProperty_step
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : ℕ) (hp : p.Prime)
    (C : TopologicalSpace.Closeds (Spec (CommRingCat.of R)))
    (ih : ∀ D < C, NoetherClosedPerfectCechProperty (Spec (CommRingCat.of R)) p hp D) :
    NoetherClosedPerfectCechProperty (Spec (CommRingCat.of R)) p hp C := by
  classical
  have hred {Z : Scheme.{u}} [IsAffine Z] [_root_.AlgebraicGeometry.IsNoetherian Z]
      [_root_.AlgebraicGeometry.IsReduced Z] [Nonempty Z]
      (jZ : Z ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion jZ]
      (hjZ : Set.range jZ = (C : Set (Spec (CommRingCat.of R))))
      {W : Scheme.{u}} (fZ : W ⟶ Z) [IsProper fZ] [Surjective fZ] :
      PerfectCechUniversalDescent p hp fZ := by
    obtain ⟨U, J, hU, hJU, hproper, hsurj, hiso, W', q, k,
      hqp, hflat, hqsurj, hqfp, hcomm⟩ :=
        exists_proper_fppf_blowup_refinement_of_proper_surjective fZ
    haveI : IsProper (blowupπ J) := hproper
    haveI : Surjective (blowupπ J) := hsurj
    haveI : IsProper q := hqp
    haveI : Flat q := hflat
    haveI : Surjective q := hqsurj
    haveI : LocallyOfFinitePresentation q := hqfp
    have hJ : Dense (centerComplement J).carrier := by rw [hJU]; exact hU
    have hb := perfectCechUniversalDescent_blowup_of_center J p hp
      (noetherClosed_center_input p hp C ih jZ hjZ J hJ)
    haveI : (blowup J).IsSeparated := ⟨by
      rw [← terminal.comp_from (blowupπ J)]; infer_instance⟩
    haveI : CompactSpace W' := QuasiCompact.compactSpace_of_compactSpace q
    obtain ⟨A, hA, a, haFlat, haSurj, haFp, haAffine⟩ :=
      exists_affine_flatSurjective_refinement q
    haveI : IsAffine A := hA
    let qA := a ≫ q
    haveI : Flat qA := haFlat
    haveI : Surjective qA := haSurj
    haveI : LocallyOfFinitePresentation qA := haFp
    haveI : IsAffineHom qA := haAffine
    let S := Γ(Z, ⊤)
    haveI : IsNoetherianRing S :=
      IsLocallyNoetherian.component_noetherian (X := Z) ⟨⊤, isAffineOpen_top Z⟩
    let r := blowupπ J ≫ Z.isoSpec.hom
    have hr : PerfectCechUniversalDescent p hp r :=
      (perfectCechUniversalDescent_targetIso p hp (blowupπ J) Z.isoSpec).mpr hb
    have hc := perfectCechUniversalDescent_affine_fppf_comp qA r p hp hr
    have hc' : PerfectCechUniversalDescent p hp (qA ≫ blowupπ J) :=
      (perfectCechUniversalDescent_targetIso p hp (qA ≫ blowupπ J) Z.isoSpec).mp
        (by simpa only [Category.assoc, r] using hc)
    have hk : (a ≫ k) ≫ fZ = qA ≫ blowupπ J := by
      rw [Category.assoc, hcomm, ← Category.assoc]
    haveI : IsAffineHom ((a ≫ k) ≫ fZ) := inferInstance
    haveI : LocallyOfFinitePresentation ((a ≫ k) ≫ fZ) := by rw [hk]; infer_instance
    apply perfectCechUniversalDescent_of_affine_refinement p hp fZ (a ≫ k)
    rw [hk]
    exact hc'
  intro Y j hj hr X f hf hs
  haveI : IsClosedImmersion j := hj
  haveI : IsProper f := hf
  haveI : Surjective f := hs
  haveI : IsAffine Y := isAffine_of_isAffineHom j
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian j
  haveI : _root_.AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  by_cases hY : IsEmpty Y
  · haveI := hY
    exact perfectCechUniversalDescent_flat_surjective p hp f
  · haveI : Nonempty Y := not_isEmpty_iff.mp hY
    let i := Y.nilradical.subschemeι
    apply perfectCechUniversalDescent_of_nil_baseChange p hp f i
    haveI : IsAffine Y.nilradical.subscheme := isAffine_of_isAffineHom i
    haveI : IsLocallyNoetherian Y.nilradical.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian i
    haveI : _root_.AlgebraicGeometry.IsNoetherian Y.nilradical.subscheme := ⟨⟩
    haveI : Nonempty Y.nilradical.subscheme := by
      obtain ⟨z, hz⟩ := i.surjective (Classical.arbitrary Y)
      exact ⟨z⟩
    have hjred : Set.range (i ≫ j) = (C : Set (Spec (CommRingCat.of R))) := by
      change Set.range (j ∘ i) = _
      rw [Set.range_comp, Set.range_eq_univ.mpr i.surjective, Set.image_univ, hr]
    exact hred (i ≫ j) hjred (pullback.snd f i)

end SerrePositivity.AlgebraicGeometry
