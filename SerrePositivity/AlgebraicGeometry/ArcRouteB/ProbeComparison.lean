module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalCech
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Valuations.ArcValuationProduct
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Descent.ArcPerfectCech

/-!
概要：BS17の完全v被覆の入力をB1の二重Čechの判定へ渡す。
方針：正本ArcRouteB.leanの条件付きの証明を、本体の現行APIと同じ型で接続する。
規約：任意の完全係数と零環を含み、残る正次数のhrowを仮定として明示する。
使われ方：2iのT06・V01〜V06。最終組み立てでhrowをP06から供給する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity
open SerrePositivity.BhattScholze.Perfectoidization
open SerrePositivity.BhattScholze.Perfectoidization.Arc
open scoped Simplicial TensorProduct
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

/-- 計画T06：2hの出口は正本と同じBS17入力の型。 -/
theorem bs17VCechInput (p : ℕ) [Fact p.Prime] : BS17VCechInput.{u} p := by
  intro A _ _ _ ι _ B _ _ _ f hf
  exact SerrePositivity.AlgebraicGeometry.cech_exact_of_vCover_perfect p B f hf

/-- 計画V01：正本の条件付きČech比較を同じ量化で移す。 -/
theorem cechExact_of_affineVCover_from_BS17
    (p : ℕ) [Fact p.Prime] (hBS17 : BS17VCechInput.{u} p)
    {A B : Type u} [CommRing A] [CommRing B] [CharP A p] [CharP B p]
    [PerfectRing A p] [PerfectRing B p] (f : A →+* B) (hf : Arc.IsAffineVCover f) :
    Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom f)) := by
  let F : PUnit.{u + 1} → Type u := fun _ => B
  let g (i : PUnit.{u + 1}) : A →+* F i := f
  have hg : IsVCoverFamily F g := by
    intro V _ _ _ k
    obtain ⟨W, hW, hv, e, l, he, hl⟩ := hf V k
    exact ⟨PUnit.unit, W, hW, hv, trivial, e, l, he, hl⟩
  let e := (RingEquiv.piUnique F).toCommRingCatIso
  let q : Arrow.mk (CommRingCat.ofHom (RingHom.pi g)) ≅ Arrow.mk (CommRingCat.ofHom f) :=
    Arrow.isoMk (Iso.refl _) e (by
      simp only [Iso.refl_hom, Category.id_comp]
      rfl)
  exact (Cech.ringCechExact_iff_of_iso
    (CosimplicialObject.augmentedCechConerve.mapIso q)).mp (hBS17 F g hg)

/-- 計画V02：正本の条件付きČech比較を同じ量化で移す。 -/
theorem cechExact_of_perfectAffineVCover_from_BS17
    (p : ℕ) [Fact p.Prime] (hBS17 : BS17VCechInput.{u} p)
    {A B : Type u} [CommRing A] [CommRing B] [PerfectRing A p] [PerfectRing B p]
    (hp : (p : A) = 0) (f : A →+* B) (hf : Arc.IsAffineVCover f) :
    Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom f)) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · let r : B →+* A :=
      { toFun := fun _ => 0
        map_zero' := rfl
        map_one' := hA.elim _ _
        map_add' := fun _ _ => hA.elim _ _
        map_mul' := fun _ _ => hA.elim _ _ }
    apply Cech.isCechExact_of_retraction _ (CommRingCat.ofHom r)
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact hA.elim _ _
  · obtain ⟨P, hP⟩ := Ideal.exists_maximal (α := A)
    let : P.IsPrime := hP.isPrime
    obtain ⟨W, hW, _, _, l, _, _⟩ := hf (CommRingCat.of P.ResidueField)
      (algebraMap A P.ResidueField)
    let : IsDomain W := hW
    let : Nontrivial B := l.domain_nontrivial
    have hpB : (p : B) = 0 := by rw [← map_natCast f, hp, map_zero]
    let : CharP A p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    let : CharP B p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpB
    exact cechExact_of_affineVCover_from_BS17 p hBS17 f hf

/-- 計画V03：正本の条件付きČech比較を同じ量化で移す。 -/
theorem cechExact_valuationProbeProduct_from_BS17 (p : ℕ) [Fact p.Prime]
    (hBS17 : BS17VCechInput.{u} p) (A : Type u) [CommRing A]
    [PerfectRing A p] (hp : (p : A) = 0) :
    Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom (Arc.valuationProbeProductMap A))) := by
  let := valuationProbeProduct_perfectRing A p hp
  exact cechExact_of_perfectAffineVCover_from_BS17 p hBS17 hp
    (valuationProbeProductMap A) (valuationProbeProduct_vCover A)

/-- 計画V04：正本の条件付きČech比較を同じ量化で移す。 -/
theorem isAffineVCover_tensor {A B D : Type u}
    [CommRing A] [CommRing B] [CommRing D] [Algebra A B] [Algebra A D]
    (h : Arc.IsAffineVCover (algebraMap A B)) :
    Arc.IsAffineVCover (algebraMap D (D ⊗[A] B)) := by
  intro V _ _ k
  obtain ⟨W, hW, hv, e, l, he, hl⟩ := h V (k.comp (algebraMap A D))
  have hc (a : A) : (e.comp k) (algebraMap A D a) = l (algebraMap A B a) :=
    (DFunLike.congr_fun hl a).symm
  let r := coefficientTensorLift (e.comp k) l hc
  refine ⟨W, hW, hv, e, r, he, ?_⟩
  apply RingHom.ext
  intro d
  change r (d ⊗ₜ[A] (1 : B)) = (e.comp k) d
  rw [coefficientTensorLift_tmul, map_one, mul_one]

/-- 計画V05：正本の条件付きČech比較を同じ量化で移す。 -/
theorem cechExact_valuationProbeProduct_tensor_from_BS17
    (p : ℕ) [Fact p.Prime] (hBS17 : BS17VCechInput.{u} p)
    (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    [PerfectRing A p] [PerfectRing D p] (hp : (p : A) = 0) :
    let R := ∀ t : Arc.ValuationProbeIndex A, Arc.ValuationProbe A t
    letI : Algebra A R := (Arc.valuationProbeProductMap A).toAlgebra
    Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom (algebraMap D (D ⊗[A] R)))) := by
  let R := ∀ t : ValuationProbeIndex A, ValuationProbe A t
  let : Algebra A R := (valuationProbeProductMap A).toAlgebra
  change Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom (algebraMap D (D ⊗[A] R))))
  let : PerfectRing R p := valuationProbeProduct_perfectRing A p hp
  let : PerfectRing (D ⊗[A] R) p := perfectTensor_of_primeCast_eq_zero p A D R hp
  have hd : (p : D) = 0 := by rw [← map_natCast (algebraMap A D), hp, map_zero]
  exact cechExact_of_perfectAffineVCover_from_BS17 p hBS17 hd _
    (isAffineVCover_tensor (valuationProbeProduct_vCover A))

/-- 計画V06：正本の条件付きČech比較を同じ量化で移す。 -/
theorem cechExact_of_valuationProbeTests (p : ℕ) [Fact p.Prime]
    (hBS17 : BS17VCechInput.{u} p) {A : Type u} [CommRing A]
    (B : Under (CommRingCat.of A)) [PerfectRing A p] [PerfectRing B.right p]
    (hp : (p : A) = 0)
    (hrow : ∀ j, 0 < j → Cech.IsCechExact (Cech.changeToTerm
      (Under.mk (CommRingCat.ofHom (Arc.valuationProbeProductMap A))) B j)) :
    Cech.IsCechExact (Arrow.mk B.hom) := by
  let R := Under.mk (CommRingCat.ofHom (valuationProbeProductMap A))
  apply (Cech.isCechExact_iff_of_tensorCech B R hrow ?_).mpr
    (cechExact_valuationProbeProduct_from_BS17 p hBS17 A hp)
  intro i hi
  cases i with
  | zero => omega
  | succ i =>
    let D := (Cech.underCech B).right.obj ⦋i⦌
    let : Algebra A D := RingHom.toAlgebra D.hom.hom
    let : PerfectRing (Arrow.mk B.hom).left p := ‹PerfectRing A p›
    let : PerfectRing (Arrow.mk B.hom).right p := ‹PerfectRing B.right p›
    let : PerfectRing D p := Cech.cechConerve_perfectRing p (Arrow.mk B.hom) hp ⦋i⦌
    exact cechExact_valuationProbeProduct_tensor_from_BS17 p hBS17 A D hp

end SerrePositivity.AlgebraicGeometry.ArcRouteB
