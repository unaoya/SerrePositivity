module

public import SerrePositivity.AlgebraicGeometry.NilImmersionPerfectCechPullback
public import SerrePositivity.AlgebraicGeometry.NilBaseChangeCechNerve
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleAugmentedPullback
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleDouble
public import SerrePositivity.AlgebraicGeometry.FiniteFiberPowerSucc
public import SerrePositivity.AlgebraicGeometry.FiniteFiberPowerUnit
public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
概要：nil 基底変更の実際のタプル増大図式と total の同型を作る。
方針：各 nerve の閉厚化と同じ逆像被覆の等式、元の基底環の Frobenius 写像を使う。
規約：中心・係数・増大項を同じ写像で保持し、Noether 性は使わない。
使われ方：被約化の反映と Noether 閉像の帰納（計画 N05・N06）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false

/-- nil 基底変更の、元の係数と逆像タプル被覆を使う増大図式の射は同型。 -/
theorem nilBaseChange_tupleAugmentedPullback_isIso
    {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
    [IsSeparated g] (F : Arrow.mk f ⟶ Arrow.mk g)
    (H : IsPullback F.left f g F.right)
    [IsClosedImmersion F.right] [Surjective F.right]
    (q : R →+* S) (hq : F.right = Spec.map (CommRingCat.ofHom q))
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) :
    IsIso (schemePerfectCechTupleAugmentedPullback f g F q hq U p hp hR hS) := by
  let vq := Spec.map (CommRingCat.ofHom q)
  letI : IsClosedImmersion vq := by
    change IsClosedImmersion (Spec.map (CommRingCat.ofHom q))
    rw [← hq]
    infer_instance
  letI : Surjective vq := by
    change Surjective (Spec.map (CommRingCat.ofHom q))
    rw [← hq]
    infer_instance
  letI : (RingHom.toMorphismProperty (fun φ ↦ Function.Surjective φ)).RespectsIso := by
    rw [← RingHom.toMorphismProperty_respectsIso_iff]
    exact RingHom.surjective_respectsIso
  have hqs : Function.Surjective q :=
    (MorphismProperty.arrow_mk_iso_iff
      (RingHom.toMorphismProperty (fun φ ↦ Function.Surjective φ))
      (arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom q))).mpr
        (vq.app_surjective ⊤ (isAffineOpen_top _))
  have hqt : Function.Surjective (PrimeSpectrum.comap q) :=
    (surjective_iff vq).mp inferInstance
  have hqk : RingHom.ker q ≤ nilradical R :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical q).mp hqt.denseRange
  have hqu := SerrePositivity.CommutativeAlgebra.isUniversalHomeomorphism_of_nil_kernel q hqs hqk
  haveI : IsIso (ModuleCat.ofHom
      (frobeniusDirectLimitMap p hp hR hS q).toAddMonoidHom.toIntLinearMap) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (frobeniusDirectLimitUniversalHomeomorphism_bijective p hp hR hS q hqu)
  have hsep : ∀ n : ℕ, IsSeparated (WidePullback.base (fun _ : Fin (n + 1) ↦ g)) := by
    intro n
    induction n with
    | zero =>
      rw [← finiteFiberPowerZeroIso_hom_base g]
      infer_instance
    | succ n ih =>
      let v := WidePullback.lift (WidePullback.base (fun _ : Fin (n + 1 + 1) ↦ g))
        (fun j : Fin (n + 1) ↦ WidePullback.π (fun _ : Fin (n + 1 + 1) ↦ g) j.succ)
        (fun j ↦ WidePullback.π_arrow (fun _ : Fin (n + 1 + 1) ↦ g) j.succ)
      letI : IsSeparated v := MorphismProperty.of_isPullback
        (isPullback_finiteFiberPowerSucc g n).flip (inferInstance : IsSeparated g)
      letI : IsSeparated (WidePullback.base (fun _ : Fin (n + 1) ↦ g)) := ih
      have he : v ≫ WidePullback.base (fun _ : Fin (n + 1) ↦ g) =
          WidePullback.base (fun _ : Fin (n + 1 + 1) ↦ g) := WidePullback.lift_base _ _ _ _
      rw [← he]
      infer_instance
  let M := schemePerfectCechTupleAugmentedPullback f g F q hq U p hp hR hS
  haveI : IsIso M.left := by dsimp [M, schemePerfectCechTupleAugmentedPullback]; infer_instance
  haveI : ∀ n : SimplexCategory, IsIso (M.right.app n) := fun n ↦ by
    let v := (Arrow.mapCechNerve F).app (op n)
    letI : IsClosedImmersion v := (nilBaseChange_cechNerve_map F H (op n)).1
    letI : Surjective v := (nilBaseChange_cechNerve_map F H (op n)).2
    letI : IsSeparated (WidePullback.base (fun _ : Fin (n.len + 1) ↦ g)) := hsep n.len
    letI : ((Arrow.mk g).cechNerve.obj (op n)).IsSeparated := ⟨by
      change IsSeparated (terminal.from (widePullback (Spec (CommRingCat.of R))
        (fun _ : Fin (n.len + 1) ↦ Y) (fun _ ↦ g)))
      rw [← terminal.comp_from (WidePullback.base (fun _ : Fin (n.len + 1) ↦ g))]
      infer_instance⟩
    let hg := schemeCechNervePresheaf_primeCast g p hR (op n)
    let hf := schemeCechNervePresheaf_primeCast f p hS (op n)
    let P := frobeniusRingDiagram ((Arrow.mk f).cechNerve.obj (op n)).presheaf p hp hf
    let W := schemeCechTupleOpen g U (op n)
    let A := fun t ↦ v ⁻¹ᵁ W t
    let B := schemeCechTupleOpen f (fun i ↦ F.left ⁻¹ᵁ U i) (op n)
    have e : A = B := funext fun t ↦
      (schemeCechTupleOpen_mapCechNerve_preimage F U (op n) t).symm
    have hRef : ∀ hb : ∀ t, B t ≤ A t,
        IsIso (openCoverCechRefinementMap P A B id hb) :=
      Eq.rec (motive := fun B _ ↦ ∀ hb : ∀ t, B t ≤ A t,
        IsIso (openCoverCechRefinementMap P A B id hb))
        (by intro hb; rw [openCoverCechRefinementMap_id]; infer_instance) e
    haveI : IsIso (schemeStructurePerfectCechPullbackMap v p hp hg hf W) :=
      nilImmersion_perfectCechPullback_isIso v p hp hg hf W
        (schemeCechTupleOpen_isAffine g U hU n.len)
    haveI : IsIso (openCoverCechRefinementMap P A B id
        (fun t ↦ le_of_eq (schemeCechTupleOpen_mapCechNerve_preimage F U (op n) t))) := hRef _
    change IsIso (schemeStructurePerfectCechPullbackMap v p hp hg hf W ≫
      openCoverCechRefinementMap P A B id
        (fun t ↦ le_of_eq (schemeCechTupleOpen_mapCechNerve_preimage F U (op n) t)))
    infer_instance
  haveI : IsIso M.right := NatIso.isIso_of_isIso_app _
  let e := Comma.isoMk (asIso M.left) (asIso M.right) M.w
  have he : e.hom = M := by apply Comma.hom_ext <;> rfl
  change IsIso M
  rw [← he]
  infer_instance

/-- 同じ nil 基底変更の増大図式の同型は、元の total の完全性を保ち反映する。 -/
theorem nilBaseChange_tupleTotal_acyclic_iff
    {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
    [IsSeparated g] (F : Arrow.mk f ⟶ Arrow.mk g)
    (H : IsPullback F.left f g F.right)
    [IsClosedImmersion F.right] [Surjective F.right]
    (q : R →+* S) (hq : F.right = Spec.map (CommRingCat.ofHom q))
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleDouble g U p hp hR) (ComplexShape.up ℕ)).Acyclic ↔
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleDouble f (fun i ↦ F.left ⁻¹ᵁ U i) p hp hS)
      (ComplexShape.up ℕ)).Acyclic := by
  letI := nilBaseChange_tupleAugmentedPullback_isIso f g F H q hq p hp hR hS U hU
  let e := cechIntegerLiftTotalFunctor.mapIso
    (SerrePositivity.Cech.augmentedCochain.mapIso
      (asIso (schemePerfectCechTupleAugmentedPullback f g F q hq U p hp hR hS)))
  constructor
  · intro h n
    exact (h n).of_iso e
  · intro h n
    exact (h n).of_iso e.symm

end SerrePositivity.AlgebraicGeometry
