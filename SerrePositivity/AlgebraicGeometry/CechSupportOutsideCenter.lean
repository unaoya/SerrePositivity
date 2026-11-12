module

public import SerrePositivity.AlgebraicGeometry.CenterComplementLocalization
public import SerrePositivity.AlgebraicGeometry.AffineBaseChangeCechVanishing
public import SerrePositivity.AlgebraicGeometry.SupportFromLocalizedTensor
public import Mathlib.RingTheory.Flat.Localization

/-!
概要：中心外で同型な射の正次数の構造層 Čech H の台は中心内。
方針：中心外の各素点へ局所化し、実際の同型な底変換で消滅を示す。
規約：有限アフィン被覆と分離性の条件を明示する。
使われ方：射影有限性と合わせ、中心の冪による零化を得る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable [IsAffineHom (pullback.diagonal (terminal.from X))]
variable (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
variable [IsIso (f ∣_ affineCenterComplement I)]
variable {ι : Type} [LinearOrder ι] [Fintype ι]
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤)

include hU hcU in
/-- 中心外で同型な射の正次数 Čech H の台は中心内。BST13 Lemma 3.9 の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem schemeCechSupport_subset_of_isoOffCenter (q : ℕ) (hq : 0 < q) :
    Module.support R ((fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf X ⋙
      ModuleCat.restrictScalars (schemeScalarHom X f)) U)).homology q) ⊆
        PrimeSpectrum.zeroLocus (I : Set R) := by
  apply support_subset_of_localizedTensor_subsingleton
  intro P hP
  let A := Localization P.asIdeal.primeCompl
  let g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R A))
  let iY := pullback.snd f g
  let j := pullback.fst f g
  letI : IsIso iY := pullback_localization_isIso_of_centerComplement f I P hP
  letI : IsAffine (pullback f g) := isAffine_of_isAffineHom iY
  letI : IsAffineHom j := MorphismProperty.pullback_fst f g
    (inferInstance : IsAffineHom g)
  have hflat : (algebraMap R A).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A P.asIdeal.primeCompl)
  have hz := affineBaseChangeCechHomology_isZero f iY j (IsPullback.of_hasPullback f g) U
    hflat hU (fun i ↦ (hU i).preimage j) (j.iSup_preimage_eq_top hcU) q hq
  let e : ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A)) ≃ₗ[R] A :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r a ↦ (Algebra.smul_def r (show A from a)).symm }
  let M := (fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf X ⋙
    ModuleCat.restrictScalars (schemeScalarHom X f)) U)).homology q
  letI : Subsingleton (TensorProduct R
      ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A)) M) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  exact (TensorProduct.congr e (LinearEquiv.refl R _)).symm.injective.subsingleton

end SerrePositivity.AlgebraicGeometry
