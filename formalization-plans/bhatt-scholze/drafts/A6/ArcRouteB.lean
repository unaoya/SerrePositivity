module

public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Valuations.ArcValuationProduct
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Descent.ArcCechUltraproduct
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Descent.ArcCechOverlap
public import SerrePositivity.CommutativeAlgebra.ValuationInterval.Endpoint
public import SerrePositivity.CommutativeAlgebra.ValuationInterval.FinitePresentation
public import SerrePositivity.CommutativeAlgebra.ValuationInterval.Zorn
public import SerrePositivity.HomologicalAlgebra.Cech.Composition
public import SerrePositivity.HomologicalAlgebra.Cech.Filtered

/-!
概要：BS-W12 の B6 の型と BS17 の入力の接続。
方針：有限族の v 降下を一射に移し、B1 の二重 Čech 比較に渡す型を確認する。
規約：このファイルは drafts の区切り。被覆の型は ArcSheafProperty.lean と同じ。
使われ方：⑥の BS17 Theorem 4.1 (i) が本体に入った後の G-A6-1 の組み立て。
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived.W12RouteB

set_option backward.isDefEq.respectTransparency false

/-- ArcSheafProperty.lean と同じ、指定した階数で試す被覆族。 -/
def ValuativeCoverFamily (rank : CommRingCat.{u} → Prop)
    {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  ∀ (V : CommRingCat.{u}) [IsDomain V] [ValuationRing V], rank V → ∀ k : A →+* V,
    ∃ (i : ι) (W : CommRingCat.{u}) (hW : IsDomain W),
      letI : IsDomain W := hW
      ValuationRing W ∧ rank W ∧ ∃ (e : V →+* W) (l : B i →+* W),
        e.FaithfullyFlat ∧ l.comp (f i) = e.comp k

/-- 有限族の v 被覆（BS17 Definition 2.1）。 -/
def IsVCoverFamily {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  ValuativeCoverFamily (fun _ => True) B f

/-- 標数 p で使う有限族の arc 被覆（BM18 Definition 1.2）。 -/
def IsArcCoverFamilyCharP {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  ValuativeCoverFamily (fun V => ringKrullDim V ≤ 1) B f

/-- 有限族を積への一射にして作る増大 Čech 余脈体。 -/
def affineFamilyCech {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) :
    CosimplicialObject.Augmented CommRingCat.{u} :=
  (Arrow.mk (CommRingCat.ofHom (RingHom.pi f))).augmentedCechConerve

/-- ⑥が閉じる入力の型（BS17 Theorem 4.1 (i)、構造層）。
drafts/A6/ArcSheafProperty.lean の cech_exact_of_vCover_perfect に対応する。 -/
def BS17VCechInput (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ {A : Type u} [CommRing A] [CharP A p] [PerfectRing A p]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    [∀ i, CharP (B i) p] [∀ i, PerfectRing (B i) p]
    (f : ∀ i, A →+* B i), IsVCoverFamily B f →
    Cech.AugmentedRingCechExact (affineFamilyCech B f)

/-- B6 が閉じる G-A6-1 の型（BS 著者版 Proposition 8.10 の証明）。
有限族の型と次数の規約は元の下書きに合わせている。 -/
def ArcRouteBGoal (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ {A : Type u} [CommRing A] [CharP A p] [PerfectRing A p]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    [∀ i, CharP (B i) p] [∀ i, PerfectRing (B i) p]
    (f : ∀ i, A →+* B i), IsArcCoverFamilyCharP B f →
    Cech.AugmentedRingCechExact (affineFamilyCech B f)

/-- 有限族版の BS17 入力を B5 の一射の v 被覆に接続する。 -/
theorem cechExact_of_affineVCover_from_BS17
    (p : ℕ) [Fact p.Prime] (hBS17 : BS17VCechInput.{u} p)
    {A B : Type u} [CommRing A] [CommRing B] [CharP A p] [CharP B p]
    [PerfectRing A p] [PerfectRing B p] (f : A →+* B) (hf : IsAffineVCover f) :
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

/-- 零環を許す完全標数 p の一射に BS17 の入力を適用する。
非零の基底では、その素点の剰余体による v 被覆の試験から終域の非零性が従う。 -/
theorem cechExact_of_perfectAffineVCover_from_BS17
    (p : ℕ) [Fact p.Prime] (hBS17 : BS17VCechInput.{u} p)
    {A B : Type u} [CommRing A] [CommRing B] [PerfectRing A p] [PerfectRing B p]
    (hp : (p : A) = 0) (f : A →+* B) (hf : IsAffineVCover f) :
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

/-- B5 の積射の Čech 完全性を BS17 Theorem 4.1 (i) に帰着する。 -/
theorem cechExact_valuationProbeProduct_from_BS17 (p : ℕ) [Fact p.Prime]
    (hBS17 : BS17VCechInput.{u} p)
    (A : Type u) [CommRing A] [PerfectRing A p] (hp : (p : A) = 0) :
    Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom (valuationProbeProductMap A))) := by
  let := valuationProbeProduct_perfectRing A p hp
  exact cechExact_of_perfectAffineVCover_from_BS17 p hBS17 hp
    (valuationProbeProductMap A) (valuationProbeProduct_vCover A)

/-- 一射の v 被覆は任意の底変換で保たれる（BM18 Proposition 3.30 の使用箇所）。 -/
theorem isAffineVCover_tensor
    {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra A D] (h : IsAffineVCover (algebraMap A B)) :
    IsAffineVCover (algebraMap D (D ⊗[A] B)) := by
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

private theorem perfectTensor_of_p_eq_zero
    (p : ℕ) [Fact p.Prime] (A D B : Type u) [CommRing A] [CommRing D] [CommRing B]
    [Algebra A D] [Algebra A B] [PerfectRing A p] [PerfectRing D p] [PerfectRing B p]
    (hp : (p : A) = 0) : PerfectRing (D ⊗[A] B) p := by
  have hzero {T : Type u} [CommRing T] (f : T →+* D ⊗[A] B) (hT : Subsingleton T) :
      PerfectRing (D ⊗[A] B) p := by
    have hz : (0 : D ⊗[A] B) = 1 := by
      rw [← map_zero f, ← map_one f, hT.elim (0 : T) 1]
    let h := subsingleton_of_zero_eq_one hz
    exact ⟨⟨fun _ _ _ => h.elim _ _, fun x => ⟨0, h.elim _ _⟩⟩⟩
  rcases subsingleton_or_nontrivial D with hD | hD
  · exact hzero (algebraMap D (D ⊗[A] B)) hD
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact hzero (Algebra.TensorProduct.includeRight : B →ₐ[A] D ⊗[A] B).toRingHom hB
  let : Nontrivial A := (algebraMap A D).domain_nontrivial
  have hd : (p : D) = 0 := by rw [← map_natCast (algebraMap A D), hp, map_zero]
  have hb : (p : B) = 0 := by rw [← map_natCast (algebraMap A B), hp, map_zero]
  let : CharP A p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
  let : CharP D p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hd
  let : CharP B p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hb
  exact perfectCoefficientTensor_perfectRing p A D B

/-- B5 の積射を任意の完全係数へ底変換したときの Čech 完全性を BS17 に帰着する。 -/
theorem cechExact_valuationProbeProduct_tensor_from_BS17
    (p : ℕ) [Fact p.Prime] (hBS17 : BS17VCechInput.{u} p)
    (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    [PerfectRing A p] [PerfectRing D p] (hp : (p : A) = 0) :
    let R := ∀ t : ValuationProbeIndex A, ValuationProbe A t
    letI : Algebra A R := (valuationProbeProductMap A).toAlgebra
    Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom (algebraMap D (D ⊗[A] R)))) := by
  let R := ∀ t : ValuationProbeIndex A, ValuationProbe A t
  let : Algebra A R := (valuationProbeProductMap A).toAlgebra
  change Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom (algebraMap D (D ⊗[A] R))))
  let : PerfectRing R p := valuationProbeProduct_perfectRing A p hp
  let : PerfectRing (D ⊗[A] R) p := perfectTensor_of_p_eq_zero p A D R hp
  have hd : (p : D) = 0 := by rw [← map_natCast (algebraMap A D), hp, map_zero]
  exact cechExact_of_perfectAffineVCover_from_BS17 p hBS17 hd _
    (isAffineVCover_tensor (valuationProbeProduct_vCover A))

/-- B6 の最後の比較（BM18 Lemma 3.4 と Proposition 4.8）。
⑥の BS17 入力を与えると、残る側は積射の Čech 項での B の底変換の完全性。 -/
theorem cechExact_of_valuationProbeTests
    (p : ℕ) [Fact p.Prime] (hBS17 : BS17VCechInput.{u} p)
    {A : Type u} [CommRing A] (B : Under (CommRingCat.of A))
    [PerfectRing A p] [PerfectRing B.right p] (hp : (p : A) = 0)
    (hrow : ∀ j, 0 < j → Cech.IsCechExact (Cech.changeToTerm
      (Under.mk (CommRingCat.ofHom (valuationProbeProductMap A))) B j)) :
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

end SerrePositivity.BhattScholze.Perfectoidization.Derived.W12RouteB
