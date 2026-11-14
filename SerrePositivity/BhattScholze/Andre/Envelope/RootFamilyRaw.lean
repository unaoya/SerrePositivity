module

public import SerrePositivity.BhattScholze.Delta.Division.Family
public import SerrePositivity.BhattScholze.Andre.Envelope.PDivision
public import SerrePositivity.BhattScholze.Andre.Envelope.RootRelation
public import SerrePositivity.BhattScholze.Delta.Division.Source
public import SerrePositivity.BhattScholze.Andre.Envelope.JetRegularity
public import Mathlib.RingTheory.TensorProduct.Quotient
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# 根の関係の生の p 除算包：正則性と mod p・完備化の比較

## 概要
独立根関係の有限族・任意族の raw p 除算包の p 正則性、Frobenius 根関係の係数商、raw 包の mod p 商の忠実平坦性・係数射に沿う底変換・Koszul 比較・高次 Tor の消滅・導来完備化と mod p の比較。
BS 著者版 Corollary 2.39 と Remark 7.15 の包を根の族に沿って扱うため、raw 包の正則性と剰余を比較する。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/RootFamilySource`、`Envelope/RootResidueKoszul`、`Variants/RootedExtension`。
-/

universe u v w

/-! ## 独立根関係の任意有限族のraw p除算包のp正則性 -/

@[expose] public noncomputable section DeltaRootFiniteRawRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

/-- 有限先行集合と一元添字の直和は一添字追加後の集合に標準同定される。 -/
def deltaRootFiniteInsertIndexEquiv {σ : Type v} [DecidableEq σ] {η : Type w} [Unique η]
    (T : Finset σ) (s : σ) (hs : s ∉ T) : (T : Type v) ⊕ η ≃ (insert s T : Finset σ) := by
  classical
  exact
    { toFun := fun r ↦ match r with
        | Sum.inl t => ⟨t, Finset.mem_insert_of_mem t.property⟩
        | Sum.inr _ => ⟨s, Finset.mem_insert_self s T⟩
      invFun := fun r ↦ if h : (r : σ) ∈ T then Sum.inl ⟨r, h⟩ else Sum.inr default
      left_inv := by
        intro r
        cases r with
        | inl t => dsimp; rw [ite_eq_left t.property]
        | inr r =>
          dsimp
          rw [dite_eq_right hs]
          congr 1
          exact Subsingleton.elim _ _
      right_inv := by
        intro r
        by_cases h : (r : σ) ∈ T
        · dsimp
          rw [dite_eq_left h]
        · dsimp
          rw [dite_eq_right h]
          apply Subtype.ext
          exact ((Finset.mem_insert.mp r.property).resolve_right h).symm }

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable {η : Type (max u v)} [Unique η]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b

/-- 任意有限集合の独立根関係のFrobenius像を同時p除算したraw環はp正則。
各有限先行集合の二種類のghost単射は明示仮定として保持する。 -/
theorem deltaRootFiniteRaw_p_mul_injective
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : ∀ T : Finset σ, Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T))
    (hg₁ : ∀ T : Finset σ,
      Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
        (p : DeltaAdjoinDivision E (p : P)
          (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) →
      Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing
        (R := DeltaAdjoinDivision E (p : P) (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η) →
      ℕ → RelativeFreeDeltaRing
        (R := DeltaAdjoinDivision E (p : P) (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η))
    (T : Finset σ) :
    Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
      (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
      (p : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) := by
  classical
  have hpP : Function.Injective (fun z : P ↦ (p : P) * z) := by
    have h : IsSMulRegular A (p : A) := hpA
    have h' : IsSMulRegular P (p : P) := by simpa only [map_natCast] using h.of_flat (S := P)
    exact h'
  let wP := w.map (MvPolynomial.C : A →+* P).toMonoidHom
  have hwP : (wP : P) = (E).delta (p : P) := by
    change MvPolynomial.C (w : A) = _
    rw [hw, ← polynomialRankOneDeltaStructure_delta_C σ D (p : A), map_natCast]
  induction T using Finset.induction_on with
  | empty =>
    let e := deltaAdjoinDivisionEmptyEquiv E (p : P)
      (fun t : (∅ : Finset σ) ↦ DeltaStructure.frobeniusLift E (r t))
    intro z t hzt
    apply e.injective
    apply hpP
    simpa only [map_mul, map_natCast] using congrArg e hzt
  | @insert s T hs ih =>
    have hx : IsSMulRegular
        (P ⧸ deltaDivisionFirstBaseIdeal (p := p) (p : P) (fun t : T ↦ r t ^ p))
        (Ideal.Quotient.mk
          (deltaDivisionFirstBaseIdeal (p := p) (p : P) (fun t : T ↦ r t ^ p)) (r s)) := by
      have hpp : Ideal.span {(p : P), (p : P)} = Ideal.span {(p : P)} :=
        congrArg Ideal.span (Set.insert_eq_of_mem (Set.mem_singleton (p : P)))
      rw [deltaDivisionFirstBaseIdeal, hpp]
      exact deltaRootPowerSubsetModP_remaining_isSMulRegular (p := p) (T : Set σ) b s hs
    have hstep := deltaPDivisionFamilySum_p_mul_injective (η := η) E (fun t : T ↦ r t)
      (r s) hpP ih (hg₀ T) (hg₁ T ih) wP hwP hx
    let ρ := deltaRootFiniteInsertIndexEquiv (η := η) T s hs
    let e := deltaAdjoinDivisionReindexEquiv E (p : P)
      (Sum.elim (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))
        (fun _ : η ↦ DeltaStructure.frobeniusLift E (r s)))
      (fun t : (insert s T : Finset σ) ↦ DeltaStructure.frobeniusLift E (r t)) ρ
      (fun t ↦ by cases t <;> rfl)
    intro z t hzt
    apply e.symm.injective
    apply hstep
    simpa only [map_mul, map_natCast] using congrArg e.symm hzt

end SerrePositivity.BhattScholze

end DeltaRootFiniteRawRegular

/-! ## 任意根関係族のraw p除算包のp正則性 -/

@[expose] public noncomputable section DeltaRootFamilyRawRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable {η : Type (max u v)} [Unique η]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b

/-- 任意添字族のraw包は、有限部分集合版の証明と標準余極限比較からp正則となる。
ghost入力は先行raw包のp正則性を受け取る形で保持し、循環依存を作らない。 -/
theorem deltaRootFamilyRaw_p_mul_injective
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : ∀ T : Finset σ, Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T))
    (hg₁ : ∀ T : Finset σ,
      Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
        (p : DeltaAdjoinDivision E (p : P)
          (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) →
      Function.Injective (WittVector.ghostMap :
        WittVector p (RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η) →
        ℕ → RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η)) :
    Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
      (fun t : σ ↦ DeltaStructure.frobeniusLift E (r t)) ↦
      (p : DeltaAdjoinDivision E (p : P)
        (fun t : σ ↦ DeltaStructure.frobeniusLift E (r t))) * z) := by
  apply deltaAdjoinDivisionFamily_p_mul_injective E (p : P)
    (fun t : σ ↦ DeltaStructure.frobeniusLift E (r t))
  intro T
  exact deltaRootFiniteRaw_p_mul_injective (η := η) D b hpA w hw hg₀ hg₁ T

end SerrePositivity.BhattScholze

end DeltaRootFamilyRawRegular

/-! ## Frobenius根関係の係数商のp²乗根表示と忠実平坦性 -/

@[expose] public noncomputable section DeltaRootFrobeniusCoefficient

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 標数pで全根関係のp乗は指数p²のモニック関係式イデアルを与える。 -/
theorem deltaRootPowerRelationIdeal_eq_monic (hp : (p : A) = 0) (b : σ → A) :
    Ideal.span (Set.range fun s ↦ (deltaRootRelationFamily (p := p) b s) ^ p) =
      monicPowerFamilyRelationIdeal (p * p) σ A (fun s ↦ b s ^ p) := by
  have hrange (f : σ → MvPolynomial σ A) :
      Set.range (fun s : (Set.univ : Set σ) ↦ f s) = Set.range f := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s, Set.mem_univ s⟩, rfl⟩
  have h := deltaRootSubset_powerRelationIdeal_eq hp (Set.univ : Set σ) b
  unfold deltaRootSubsetRelationIdeal at h
  rw [hrange (fun s ↦ (deltaRootRelationFamily (p := p) b s) ^ p),
    hrange (deltaRootRelationFamily (p := p * p) (fun s ↦ b s ^ p))] at h
  exact h

variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "a" => fun s ↦ DeltaStructure.frobeniusLift E (r s)
local notation "I" => Ideal.span {(p : A)}
local notation "QA" => A ⧸ I
local notation "c" => fun s ↦ (Ideal.Quotient.mk I (b s)) ^ p
local notation "C" => MonicPowerFamilyCover (p * p) σ QA c
local notation "J" => deltaDivisionFirstBaseIdeal (p := p) (p : P) a

/-- raw Frobenius除算の初期係数商。 -/
abbrev DeltaRootFrobeniusCoefficientQuotient := P ⧸ J

/-- 初期係数イデアルは係数のpと先行根関係のp乗で生成される。 -/
theorem deltaRootFrobeniusCoefficientIdeal_eq :
    J = (I).map (MvPolynomial.C : A →+* P) ⊔ Ideal.span
      (Set.range fun s : (Set.univ : Set σ) ↦ (r s) ^ p) := by
  rw [deltaPDivisionFirstBaseIdeal_frobenius_eq_power]
  unfold deltaDivisionFirstBaseIdeal
  have hpp : Ideal.span {(p : P), (p : P)} = Ideal.span {(p : P)} :=
    congrArg Ideal.span (Set.insert_eq_of_mem (Set.mem_singleton (p : P)))
  rw [hpp]
  simp only [Ideal.map_span, Set.image_singleton, map_natCast]
  congr 1
  congr 1
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, Set.mem_univ s⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩

/-- 標準p商の上で、根関係p乗イデアルは指数p²の通常根関係に一致する。 -/
theorem deltaRootFrobeniusCoefficientResidueIdeal_eq :
    Ideal.span (Set.range fun s : (Set.univ : Set σ) ↦
      (deltaRootRelationFamily (p := p) (fun t ↦ Ideal.Quotient.mk I (b t)) s) ^ p) =
      monicPowerFamilyRelationIdeal (p * p) σ QA c := by
  have hp : (p : QA) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hrange : Set.range (fun s : (Set.univ : Set σ) ↦
      (deltaRootRelationFamily (p := p) (fun t ↦ Ideal.Quotient.mk I (b t)) s) ^ p) =
      Set.range (fun s : σ ↦
        (deltaRootRelationFamily (p := p) (fun t ↦ Ideal.Quotient.mk I (b t)) s) ^ p) := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s, Set.mem_univ s⟩, rfl⟩
  rw [hrange]
  exact deltaRootPowerRelationIdeal_eq_monic hp (fun t ↦ Ideal.Quotient.mk I (b t))

/-- 初期係数商はA/p上の既存p²乗根添加環と標準同型。 -/
def deltaRootFrobeniusCoefficientEquiv : DeltaRootFrobeniusCoefficientQuotient D b ≃+* C :=
  (((Ideal.quotEquivOfEq (deltaRootFrobeniusCoefficientIdeal_eq D b)).trans
    (deltaRootPowerSubsetBaseQuotientEquiv (p := p) I Set.univ b)).trans
    (Ideal.quotEquivOfEq (deltaRootFrobeniusCoefficientResidueIdeal_eq (p := p) b))).trans
    (monicPowerFamilyPresentationEquiv (p * p) σ QA c)

/-- 標準同型は任意多項式代表元の係数をmod pへ送る公式で与えられる。 -/
theorem deltaRootFrobeniusCoefficientEquiv_mk (x : P) :
    deltaRootFrobeniusCoefficientEquiv D b (Ideal.Quotient.mk J x) =
      monicPowerFamilyQuotientMap (p * p) σ QA c
        (Ideal.Quotient.mk _ (MvPolynomial.map (Ideal.Quotient.mk I) x)) := by
  rw [deltaRootFrobeniusCoefficientEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, deltaRootPowerSubsetBaseQuotientEquiv_mk,
    Ideal.quotEquivOfEq_mk]
  rfl

/-- 初期係数商表示は元の基底係数の標準像を保つ。 -/
theorem deltaRootFrobeniusCoefficientEquiv_C (x : A) :
    deltaRootFrobeniusCoefficientEquiv D b (Ideal.Quotient.mk J (MvPolynomial.C x)) =
      algebraMap QA C (Ideal.Quotient.mk I x) := by
  rw [deltaRootFrobeniusCoefficientEquiv_mk, MvPolynomial.map_C]
  change monicPowerFamilyEvaluation (p * p) σ QA c (MvPolynomial.C _) = _
  simp [monicPowerFamilyEvaluation]

/-- 初期係数商の標準A/p係数射。 -/
def deltaRootFrobeniusCoefficientBaseMap : QA →+* DeltaRootFrobeniusCoefficientQuotient D b :=
  (deltaRootFrobeniusCoefficientEquiv D b).symm.toRingHom.comp (algebraMap QA C)

/-- 標準係数射は元の係数を二つの商の実標準像へ送る。 -/
theorem deltaRootFrobeniusCoefficientBaseMap_mk (x : A) :
    deltaRootFrobeniusCoefficientBaseMap D b (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk J (MvPolynomial.C x) := by
  apply (deltaRootFrobeniusCoefficientEquiv D b).injective
  change (deltaRootFrobeniusCoefficientEquiv D b)
    ((deltaRootFrobeniusCoefficientEquiv D b).symm _) = _
  rw [RingEquiv.apply_symm_apply, deltaRootFrobeniusCoefficientEquiv_C]

/-- 標準係数射による初期係数商のA/p代数構造。 -/
@[instance_reducible] def deltaRootFrobeniusCoefficientBaseAlgebra :
    Algebra QA (DeltaRootFrobeniusCoefficientQuotient D b) :=
  (deltaRootFrobeniusCoefficientBaseMap D b).toAlgebra

/-- 表示同型は実際のA/p係数射に関する代数同型。 -/
def deltaRootFrobeniusCoefficientAlgEquiv :
    letI := deltaRootFrobeniusCoefficientBaseAlgebra D b
    DeltaRootFrobeniusCoefficientQuotient D b ≃ₐ[QA] C := by
  let := deltaRootFrobeniusCoefficientBaseAlgebra D b
  apply AlgEquiv.ofRingEquiv (f := deltaRootFrobeniusCoefficientEquiv D b)
  intro x
  exact (deltaRootFrobeniusCoefficientEquiv D b).apply_symm_apply _

/-- 初期係数商は標準A/p係数射に関して忠実平坦。有限性・p正則性は不要。 -/
theorem deltaRootFrobeniusCoefficient_moduleFaithfullyFlat :
    letI := deltaRootFrobeniusCoefficientBaseAlgebra D b
    Module.FaithfullyFlat QA (DeltaRootFrobeniusCoefficientQuotient D b) := by
  let := deltaRootFrobeniusCoefficientBaseAlgebra D b
  let := monicPowerFamilyCover_moduleFaithfullyFlat_all (p * p) σ QA c
    (Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : p.Prime).pos)
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (deltaRootFrobeniusCoefficientAlgEquiv D b).toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaRootFrobeniusCoefficient

/-! ## 根関係のraw p除算包の実mod p商の標準係数射と忠実平坦性 -/

@[expose] public noncomputable section DeltaRootRawModPFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

variable (D : DeltaStructure p A) (b : σ → A)
variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
    ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
variable (w : Aˣ) (hw : (w : A) = D.delta (p : A))
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "a" => fun s ↦ DeltaStructure.frobeniusLift E (deltaRootRelationFamily (p := p) b s)
local notation "Q" => DeltaRootFrobeniusCoefficientQuotient D b
local notation "Res" => DeltaAdjoinDivisionResidue E (p : P) a
local notation "B" => DeltaAdjoinDivision E (p : P) a
local notation "QA" => A ⧸ Ideal.span {(p : A)}
local notation "wp" => Units.map (RingHom.toMonoidHom (MvPolynomial.C : A →+* P)) w

/-- 根関係raw残余商の標準A/p係数射。 -/
def deltaRootRawResidueBaseMap : QA →+* Res := by
  have hP : IsSMulRegular P (p : P) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P)
  have hpP : Function.Injective (fun x : P ↦ (p : P) * x) := hP
  let L := RelativeFreeDeltaRing (R := P) σ
  have hL : IsSMulRegular L (p : L) := by
    simpa only [map_natCast] using hP.of_flat (S := L)
  have hpL : Function.Injective (fun x : L ↦ (p : L) * x) := hL
  have hwp : (wp : P) = (E).delta (p : P) := by
    change MvPolynomial.C (w : A) = _
    rw [hw, ← polynomialRankOneDeltaStructure_delta_C σ D (p : A), map_natCast]
  exact (deltaAdjoinDivisionResidueBaseMap E hpP hpL hg
    (p : P) a wp hwp).comp (deltaRootFrobeniusCoefficientBaseMap D b)

/-- 残余係数射の元の係数上の具体的公式。 -/
theorem deltaRootRawResidueBaseMap_mk (x : A) :
    deltaRootRawResidueBaseMap D b hpA hg w hw (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (deltaAdjoinDivisionMap E (p : P) a (MvPolynomial.C x)) := by
  rw [deltaRootRawResidueBaseMap, RingHom.comp_apply,
    deltaRootFrobeniusCoefficientBaseMap_mk, deltaAdjoinDivisionResidueBaseMap_mk]

/-- 残余標準係数射のA/p代数構造。 -/
@[instance_reducible]
def deltaRootRawResidueBaseAlgebra : Algebra QA Res :=
  (deltaRootRawResidueBaseMap D b hpA hg w hw).toAlgebra

/-- raw残余商は標準A/p係数射に関して忠実平坦。添字集合の有限性は不要。 -/
theorem deltaRootRawResidue_moduleFaithfullyFlat :
    letI := deltaRootRawResidueBaseAlgebra D b hpA hg w hw
    Module.FaithfullyFlat QA Res := by
  have hP : IsSMulRegular P (p : P) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P)
  have hpP : Function.Injective (fun x : P ↦ (p : P) * x) := hP
  let L := RelativeFreeDeltaRing (R := P) σ
  have hL : IsSMulRegular L (p : L) := by
    simpa only [map_natCast] using hP.of_flat (S := L)
  have hpL : Function.Injective (fun x : L ↦ (p : L) * x) := hL
  have hwp : (wp : P) = (E).delta (p : P) := by
    change MvPolynomial.C (w : A) = _
    rw [hw, ← polynomialRankOneDeltaStructure_delta_C σ D (p : A), map_natCast]
  let := deltaRootFrobeniusCoefficientBaseAlgebra D b
  let := deltaAdjoinDivisionResidueBaseAlgebra E hpP hpL
    hg (p : P) a wp hwp
  let := deltaRootRawResidueBaseAlgebra D b hpA hg w hw
  have : IsScalarTower QA Q Res := IsScalarTower.of_algebraMap_eq' rfl
  let := deltaRootFrobeniusCoefficient_moduleFaithfullyFlat D b
  let := deltaAdjoinDivisionResidue_moduleFaithfullyFlat E hpP
    hpL hg (p : P) a wp hwp
  exact Module.FaithfullyFlat.trans QA Q Res

/-- 実際のraw包のp商への標準A/p係数射。 -/
def deltaRootRawModPBaseMap : QA →+* (B ⧸ Ideal.span {(p : B)}) :=
  (deltaAdjoinDivisionPQuotientResidueEquiv E a).symm.toRingHom.comp
    (deltaRootRawResidueBaseMap D b hpA hg w hw)

/-- 実mod p係数射は元の係数の実標準商像を与える。 -/
theorem deltaRootRawModPBaseMap_mk (x : A) :
    deltaRootRawModPBaseMap D b hpA hg w hw (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (deltaAdjoinDivisionMap E (p : P) a (MvPolynomial.C x)) := by
  rw [deltaRootRawModPBaseMap, RingHom.comp_apply]
  apply (deltaAdjoinDivisionPQuotientResidueEquiv E a).injective
  change (deltaAdjoinDivisionPQuotientResidueEquiv E a)
    ((deltaAdjoinDivisionPQuotientResidueEquiv E a).symm _) = _
  rw [RingEquiv.apply_symm_apply, deltaRootRawResidueBaseMap_mk,
    deltaAdjoinDivisionPQuotientResidueEquiv_mk]

/-- 実mod p標準係数射のA/p代数構造。 -/
@[instance_reducible]
def deltaRootRawModPBaseAlgebra : Algebra QA (B ⧸ Ideal.span {(p : B)}) :=
  (deltaRootRawModPBaseMap D b hpA hg w hw).toAlgebra

/-- raw(p,p)残余と実p商の標準同型はA/p代数同型。 -/
def deltaRootRawModPResidueAlgEquiv :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    letI := deltaRootRawResidueBaseAlgebra D b hpA hg w hw
    (B ⧸ Ideal.span {(p : B)}) ≃ₐ[QA] Res := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let := deltaRootRawResidueBaseAlgebra D b hpA hg w hw
  apply AlgEquiv.ofRingEquiv (f := deltaAdjoinDivisionPQuotientResidueEquiv E a)
  intro x
  change (deltaAdjoinDivisionPQuotientResidueEquiv E a)
    (deltaRootRawModPBaseMap D b hpA hg w hw x) =
      deltaRootRawResidueBaseMap D b hpA hg w hw x
  rw [deltaRootRawModPBaseMap, RingHom.comp_apply]
  exact (deltaAdjoinDivisionPQuotientResidueEquiv E a).apply_symm_apply _

/-- 根関係のraw同時p除算包の実p商は、標準A/p係数射に関して忠実平坦。 -/
theorem deltaRootRawModP_moduleFaithfullyFlat :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    Module.FaithfullyFlat QA (B ⧸ Ideal.span {(p : B)}) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let := deltaRootRawResidueBaseAlgebra D b hpA hg w hw
  let := deltaRootRawResidue_moduleFaithfullyFlat D b hpA hg w hw
  exact Module.FaithfullyFlat.of_linearEquiv QA Res
    (deltaRootRawModPResidueAlgEquiv D b hpA hg w hw).toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaRootRawModPFlat

/-! ## 元の係数射に沿う根関係raw包の実mod p基底変更 -/

@[expose] public noncomputable section DeltaRootRawCoefficientBaseChange

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "a" => fun s ↦ DeltaStructure.frobeniusLift E (deltaRootRelationFamily (p := p) b s)
local notation "B" => DeltaAdjoinDivision E (p : P) a
local notation "I" => Ideal.span {(p : A)}
local notation "QA" => A ⧸ I

/-- 元のδ係数環から多項式環を経由するraw包への実係数射。 -/
def deltaRootRawCoefficientMap : A →+* B :=
  (deltaAdjoinDivisionMap E (p : P) a).comp MvPolynomial.C

/-- 実係数射によるraw包のA代数構造。 -/
@[instance_reducible]
def deltaRootRawCoefficientAlgebra : Algebra A B :=
  inferInstance

/-- 既存のA代数構造の係数射は、公開した実係数射そのもの。 -/
theorem deltaRootRawCoefficientAlgebra_algebraMap :
    letI := deltaRootRawCoefficientAlgebra D b
    algebraMap A B = deltaRootRawCoefficientMap D b := rfl

/-- 元のp主イデアルのraw包への拡張は、raw包自身の実p主イデアル。 -/
theorem deltaRootRawCoefficient_map_span_p :
    letI := deltaRootRawCoefficientAlgebra D b
    (I).map (algebraMap A B) = Ideal.span {(p : B)} := by
  simp only [Ideal.map_span, Set.image_singleton, map_natCast]

variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
    ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
variable (w : Aˣ) (hw : (w : A) = D.delta (p : A))

/-- 元の係数pイデアルによる商とraw包の実p商の比較は標準A/p代数同型。 -/
def deltaRootRawCoefficientQuotientAlgEquiv :
    letI := deltaRootRawCoefficientAlgebra D b
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    (B ⧸ (I).map (algebraMap A B)) ≃ₐ[QA] (B ⧸ Ideal.span {(p : B)}) := by
  let := deltaRootRawCoefficientAlgebra D b
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  apply AlgEquiv.ofRingEquiv (f := Ideal.quotEquivOfEq (deltaRootRawCoefficient_map_span_p D b))
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.quotEquivOfEq (deltaRootRawCoefficient_map_span_p D b)
    (Ideal.Quotient.mk _ (deltaRootRawCoefficientMap D b x)) =
      deltaRootRawModPBaseMap D b hpA hg w hw (Ideal.Quotient.mk I x)
  rw [Ideal.quotEquivOfEq_mk, deltaRootRawModPBaseMap_mk]
  rfl

/-- 元のA→A/pに沿う通常基底変更は実raw p商と標準同型。 -/
def deltaRootRawBaseChangeModPAlgEquiv :
    letI := deltaRootRawCoefficientAlgebra D b
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    QA ⊗[A] B ≃ₐ[QA] (B ⧸ Ideal.span {(p : B)}) := by
  let := deltaRootRawCoefficientAlgebra D b
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.trans
    (deltaRootRawCoefficientQuotientAlgEquiv D b hpA hg w hw)

/-- 実基底変更同型は1⊗zをzの実p商像へ送る。 -/
theorem deltaRootRawBaseChangeModPAlgEquiv_one_tmul (z : B) :
    letI := deltaRootRawCoefficientAlgebra D b
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    deltaRootRawBaseChangeModPAlgEquiv D b hpA hg w hw ((1 : QA) ⊗ₜ[A] z) =
      Ideal.Quotient.mk (Ideal.span {(p : B)}) z := by
  let := deltaRootRawCoefficientAlgebra D b
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  change deltaRootRawCoefficientQuotientAlgEquiv D b hpA hg w hw
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm _) = _
  rw [← Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk B I z,
    AlgEquiv.symm_apply_apply]
  exact Ideal.quotEquivOfEq_mk (deltaRootRawCoefficient_map_span_p D b) z

include hpA hg hw in
/-- 元の係数射に沿う実通常mod p基底変更加群はA/p上忠実平坦。 -/
theorem deltaRootRawBaseChangeModP_moduleFaithfullyFlat :
    letI := deltaRootRawCoefficientAlgebra D b
    Module.FaithfullyFlat QA (QA ⊗[A] B) := by
  let := deltaRootRawCoefficientAlgebra D b
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let := deltaRootRawModP_moduleFaithfullyFlat D b hpA hg w hw
  exact Module.FaithfullyFlat.of_linearEquiv QA (B ⧸ Ideal.span {(p : B)})
    (deltaRootRawBaseChangeModPAlgEquiv D b hpA hg w hw).toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaRootRawCoefficientBaseChange

/-! ## 元の係数環上での根関係raw包の実p Koszul比較 -/

@[expose] public noncomputable section DeltaRootRawRelativeModPKoszul

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (b : σ → A)
attribute [local instance] deltaRootRawCoefficientAlgebra
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "a" => fun s ↦ DeltaStructure.frobeniusLift E (deltaRootRelationFamily (p := p) b s)
local notation "R₀" => DeltaAdjoinDivision E (p : P) a
local notation "J₀" => Ideal.span {(p : R₀)}
local notation "Q₀" => R₀ ⧸ J₀

/-- 具体的raw包のp列を、元の係数環A上の短複体として取る。 -/
def deltaRootRawRelativeModPPresentation : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk ((p : A) • 𝟙 (ModuleCat.of A R₀))
    (ModuleCat.ofHom (Ideal.Quotient.mkₐ A J₀).toLinearMap) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change Ideal.Quotient.mk J₀ ((p : A) • r) = 0
      rw [Algebra.smul_def, map_natCast]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))))

/-- 正則入力では、この実p列は元のA加群の短完全列。 -/
theorem deltaRootRawRelativeModPPresentation_shortExact
    (hpB : Function.Injective (fun z : R₀ ↦ (p : R₀) * z)) :
    (deltaRootRawRelativeModPPresentation D b).ShortExact where
  exact := by
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro r hr
    change Ideal.Quotient.mk J₀ r = 0 at hr
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hr)
    refine ⟨s, ?_⟩
    change (p : A) • s = r
    rw [Algebra.smul_def, map_natCast]
    exact hs.symm
  mono_f := by
    apply (ModuleCat.mono_iff_injective _).mpr
    intro r s hrs
    apply hpB
    change (p : A) • r = (p : A) • s at hrs
    have hmul (t : R₀) : (p : A) • t = (p : R₀) * t := by
      rw [Algebra.smul_def, map_natCast]
    exact (hmul r).symm.trans (hrs.trans (hmul s))
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (by
    change Function.Surjective (Ideal.Quotient.mk J₀)
    exact Ideal.Quotient.mk_surjective)

/-- 実p列を元のA加群の次数零cochain複体へ送る。 -/
def deltaRootRawRelativeModPCochainPresentation :
    ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ) :=
  (deltaRootRawRelativeModPPresentation D b).map
    (CochainComplex.singleFunctor (ModuleCat A) 0)

/-- 最初のcochain射は、元のAのpによるスカラー射そのもの。 -/
theorem deltaRootRawRelativeModPCochainPresentation_f :
    (deltaRootRawRelativeModPCochainPresentation D b).f =
      smulId (p : A) (cochainSingleZero (ModuleCat.of A R₀)) := by
  change (CochainComplex.singleFunctor (ModuleCat A) 0).map
    ((p : A) • 𝟙 (ModuleCat.of A R₀)) = _
  rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

/-- A上の実p Koszul coneから、実p商の次数零対象への標準添加写像。 -/
def deltaRootRawRelativeModPKoszulAugmentation :
    CochainComplex.mappingCone (smulId (p : A) (cochainSingleZero (ModuleCat.of A R₀))) ⟶
      cochainSingleZero (ModuleCat.of A Q₀) :=
  eqToHom (congrArg (fun f : cochainSingleZero (ModuleCat.of A R₀) ⟶
      cochainSingleZero (ModuleCat.of A R₀) ↦ CochainComplex.mappingCone f)
        (deltaRootRawRelativeModPCochainPresentation_f D b).symm) ≫
    CochainComplex.mappingCone.descShortComplex (deltaRootRawRelativeModPCochainPresentation D b)

/-- 正則入力では、元のA上の実Koszul添加写像が擬同型となる。 -/
theorem deltaRootRawRelativeModPKoszulAugmentation_quasiIso
    (hpB : Function.Injective (fun z : R₀ ↦ (p : R₀) * z)) :
    QuasiIso (deltaRootRawRelativeModPKoszulAugmentation D b) := by
  have hS : (deltaRootRawRelativeModPCochainPresentation D b).ShortExact :=
    (deltaRootRawRelativeModPPresentation_shortExact D b hpB).map_of_exact
      (CochainComplex.singleFunctor (ModuleCat A) 0)
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  dsimp only [deltaRootRawRelativeModPKoszulAugmentation]
  infer_instance

/-- 元のA→A/pで実導来還元したraw包をAへ制限すると、実R/pの次数零対象になる。 -/
def deltaRootRawRelativeDerivedModPRestrictedIso
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (hpB : Function.Injective (fun z : R₀ ↦ (p : R₀) * z)) :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {(p : A)}))).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A)}))).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)))).obj ≅
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A Q₀)).obj := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)
  have hr : IsSMulRegular A (p : A) := hpA
  have := deltaRootRawRelativeModPKoszulAugmentation_quasiIso D b hpB
  exact restrictedDerivedQuotientKoszulIso (p : A) hr X ≪≫
    (DerivedCompletion.derivedScalarConeComparison A (p : A)).app
      (cochainSingleZero (ModuleCat.of A R₀)) ≪≫
    asIso (DerivedCategory.Q.map (deltaRootRawRelativeModPKoszulAugmentation D b))

end SerrePositivity.BhattScholze

end DeltaRootRawRelativeModPKoszul

/-! ## 元のA→A/pに沿う根関係raw包の高次Tor消滅と実導来比較 -/

@[expose] public noncomputable section DeltaRootRawRelativeDerivedModP

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard deltaRootRawCoefficientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "inputs" =>
  fun s ↦ DeltaStructure.frobeniusLift E (deltaRootRelationFamily (p := p) b s)
local notation "R₀" => DeltaAdjoinDivision E (p : P) inputs
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- Aとraw包がp正則なら、元の係数環A→A/pへの実係数拡大で全高次Torは消える。 -/
theorem deltaRootRawRelativeModP_torVanishing
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hpB : Function.Injective (fun a : R₀ ↦ (p : R₀) * a)) :
    scalarExtensionTorVanishing q₀ (ModuleCat.of A R₀) := by
  change (∀ n : ℕ, 0 < n → IsZero
    (((Tor (ModuleCat.{u} A) n).obj (baseChangeScalarModule q₀)).obj (ModuleCat.of A R₀)))
  rw [← derivedModuleBaseChange_negative_homology_vanishes_iff q₀ (ModuleCat.of A R₀)]
  intro n hn
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)
  let Y := (boundedAboveDerivedBaseChange q₀).obj X
  have hni : -(n : ℤ) ≠ 0 :=
    neg_ne_zero.mpr (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hn))
  let e : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).obj
      (((boundedAboveDerivedRestrictScalars q₀).obj Y).obj)) ≅
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).obj
        ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj
          (ModuleCat.of A (R₀ ⧸ Ideal.span {(p : R₀)})))) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).mapIso
      (deltaRootRawRelativeDerivedModPRestrictedIso D b hpA hpB)
  have ht : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).obj
      ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj
        (ModuleCat.of A (R₀ ⧸ Ideal.span {(p : R₀)})))) :=
    derivedSingleHomology_isZero _ (-(n : ℤ)) hni
  have hs : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).obj
      (((boundedAboveDerivedRestrictScalars q₀).obj Y).obj)) := e.isZero_iff.mpr ht
  have hr := (derivedRestrictScalarsHomologyIso q₀ (-(n : ℤ))).app Y.obj
  have hs' : IsZero ((ModuleCat.restrictScalars q₀).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) (-(n : ℤ))).obj Y.obj)) :=
    hr.isZero_iff.mp hs
  let : Subsingleton
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) (-(n : ℤ))).obj Y.obj) :=
    ModuleCat.subsingleton_of_isZero (R := A) hs'
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) (-(n : ℤ))).obj
      Y.obj) := ModuleCat.isZero_of_subsingleton
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) (-(n : ℤ))).obj Y.obj)
  exact IsZero.of_iso hz
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) (-(n : ℤ))).mapIso
      (boundedAboveDerivedBaseChangeModuleIso q₀ (ModuleCat.of A R₀))).symm

/-- 実係数拡大の通常加群は、標準A/p作用を持つ実raw p商と線形同型。 -/
def deltaRootRawRelativeModPScalarEquiv
    (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    ((ModuleCat.extendScalars q₀).obj (ModuleCat.of A R₀)) ≃ₗ[Q₀]
      (R₀ ⧸ Ideal.span {(p : R₀)}) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  exact (deltaRootRawBaseChangeModPAlgEquiv D b hpA hg w hw).toLinearEquiv

/-- 元のA→A/pに沿う実導来還元は、実raw包/pの標準A/p加群の次数零対象。 -/
def deltaRootRawRelativeDerivedModPIso
    (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
    (hpB : Function.Injective (fun x : R₀ ↦ (p : R₀) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    (boundedAboveDerivedBaseChange q₀).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (R₀ ⧸ Ideal.span {(p : R₀)})) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso _ _
      (deltaRootRawRelativeModP_torVanishing D b hpA hpB) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso
      (deltaRootRawRelativeModPScalarEquiv D b hpA hg w hw).toModuleIso

end SerrePositivity.BhattScholze

end DeltaRootRawRelativeDerivedModP

/-! ## 元のA上の根関係raw包の実導来完備化とmod p比較 -/

@[expose] public noncomputable section DeltaRootRawRelativeCompletionModP

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard deltaRootRawCoefficientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "inputs" =>
  fun s ↦ DeltaStructure.frobeniusLift E (deltaRootRelationFamily (p := p) b s)
local notation "B" => DeltaAdjoinDivision E (p : P) inputs
local notation "QA" => A ⧸ Ideal.span {(p : A)}
local notation "qA" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 元のAがp正則なら、raw包の標準A導来完備化単位を実p還元した射は同型。 -/
theorem deltaRootRawRelativeCompletionUnit_modP_isIso
    (hpA : Function.Injective (fun x : A ↦ (p : A) * x)) :
    IsIso ((boundedAboveDerivedBaseChange qA).map
      ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)))) := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)
  have hr : IsSMulRegular A (p : A) := hpA
  let F (x : A) := IsIso ((boundedAboveDerivedBaseChange
    (Ideal.Quotient.mk (Ideal.span {x}))).map
      ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app X))
  have h : F ((p : A) ^ 1) :=
    DerivedCompletion.boundedAboveDerivedCompletion_quotient_unit_isIso A (p : A) hr 1 X
  exact Eq.mp (congrArg F (_root_.pow_one (p : A))) h

/-- 元のA上の実導来完備化を実p還元すると、標準A/p作用付きの実raw包/pとなる。 -/
def deltaRootRawRelativeCompletedDerivedModPIso
    (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
    (hpB : Function.Injective (fun x : B ↦ (p : B) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    (boundedAboveDerivedBaseChange qA).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B))) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of QA (B ⧸ Ideal.span {(p : B)})) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)
  have := deltaRootRawRelativeCompletionUnit_modP_isIso D b hpA
  exact (asIso ((boundedAboveDerivedBaseChange qA).map
      ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app X))).symm ≪≫
    deltaRootRawRelativeDerivedModPIso D b hpA hpB hg w hw

/-- 実mod p比較は元のA上の実導来完備化標準単位と両立する。 -/
theorem deltaRootRawRelativeCompletedDerivedModPIso_unit
    (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
    (hpB : Function.Injective (fun x : B ↦ (p : B) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    (boundedAboveDerivedBaseChange qA).map
        ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B))) ≫
      (deltaRootRawRelativeCompletedDerivedModPIso D b hpA hpB hg w hw).hom =
        (deltaRootRawRelativeDerivedModPIso D b hpA hpB hg w hw).hom := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)
  let f := (boundedAboveDerivedBaseChange qA).map
    ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app X)
  have := deltaRootRawRelativeCompletionUnit_modP_isIso D b hpA
  change (asIso f).hom ≫ ((asIso f).symm ≪≫
    deltaRootRawRelativeDerivedModPIso D b hpA hpB hg w hw).hom = _
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

end SerrePositivity.BhattScholze

end DeltaRootRawRelativeCompletionModP

/-! ## 任意根関係全族の実導来還元・完備化比較 -/

@[expose] public noncomputable section DeltaRootFamilyRelativeModP

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard deltaRootRawCoefficientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ η : Type u} [CommRing A] [Unique η]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "B" =>
  DeltaAdjoinDivision E (p : P) (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "QA" => A ⧸ Ideal.span {(p : A)}
local notation "qA" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 任意根関係全族では、raw包のp正則性を内部で供給して実係数拡大の全高次Torが消える。 -/
theorem deltaRootFamilyRelativeModP_torVanishing
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : ∀ T : Finset σ, Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T))
    (hg₁ : ∀ T : Finset σ,
      Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
        (p : DeltaAdjoinDivision E (p : P)
          (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) →
      Function.Injective (WittVector.ghostMap :
        WittVector p (RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η) →
        ℕ → RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η)) :
    scalarExtensionTorVanishing qA (ModuleCat.of A B) := by
  exact deltaRootRawRelativeModP_torVanishing D b hpA
    (deltaRootFamilyRaw_p_mul_injective (η := η) D b hpA w hw hg₀ hg₁)

/-- 任意根関係全族の実導来還元を実raw包/pへ同定する。raw包のp正則性は追加仮定しない。 -/
def deltaRootFamilyRelativeDerivedModPIso
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : ∀ T : Finset σ, Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T))
    (hg₁ : ∀ T : Finset σ,
      Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
        (p : DeltaAdjoinDivision E (p : P)
          (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) →
      Function.Injective (WittVector.ghostMap :
        WittVector p (RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η) →
        ℕ → RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ)) :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    (boundedAboveDerivedBaseChange qA).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of QA (B ⧸ Ideal.span {(p : B)})) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  exact deltaRootRawRelativeDerivedModPIso D b hpA
    (deltaRootFamilyRaw_p_mul_injective (η := η) D b hpA w hw hg₀ hg₁) hg w hw

/-- 任意根関係全族の元のA上の実導来完備化のmod p比較。 -/
def deltaRootFamilyRelativeCompletedDerivedModPIso
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : ∀ T : Finset σ, Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T))
    (hg₁ : ∀ T : Finset σ,
      Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
        (p : DeltaAdjoinDivision E (p : P)
          (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) →
      Function.Injective (WittVector.ghostMap :
        WittVector p (RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η) →
        ℕ → RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ)) :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    (boundedAboveDerivedBaseChange qA).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B))) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of QA (B ⧸ Ideal.span {(p : B)})) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  exact deltaRootRawRelativeCompletedDerivedModPIso D b hpA
    (deltaRootFamilyRaw_p_mul_injective (η := η) D b hpA w hw hg₀ hg₁) hg w hw

/-- 任意全族の実mod p同型は元のA上の標準実導来完備化単位と可換。 -/
theorem deltaRootFamilyRelativeCompletedDerivedModPIso_unit
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : ∀ T : Finset σ, Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T))
    (hg₁ : ∀ T : Finset σ,
      Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
        (p : DeltaAdjoinDivision E (p : P)
          (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) →
      Function.Injective (WittVector.ghostMap :
        WittVector p (RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η) →
        ℕ → RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ)) :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    (boundedAboveDerivedBaseChange qA).map
        ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B))) ≫
      (deltaRootFamilyRelativeCompletedDerivedModPIso D b hpA w hw hg₀ hg₁ hg).hom =
        (deltaRootFamilyRelativeDerivedModPIso D b hpA w hw hg₀ hg₁ hg).hom := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  exact deltaRootRawRelativeCompletedDerivedModPIso_unit D b hpA
    (deltaRootFamilyRaw_p_mul_injective (η := η) D b hpA w hw hg₀ hg₁) hg w hw

end SerrePositivity.BhattScholze

end DeltaRootFamilyRelativeModP

/-! ## 任意根関係raw包の実導来完備化のmod pホモロジーと忠実平坦性 -/

@[expose] public noncomputable section DeltaRootFamilyCompletedModPFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard deltaRootRawCoefficientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ η : Type u} [CommRing A] [Unique η]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "B" =>
  DeltaAdjoinDivision E (p : P) (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "QA" => A ⧸ Ideal.span {(p : A)}
local notation "qA" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- A上の実導来完備化の実p還元H0は、標準A/p作用付き実raw包/pと線形同値。 -/
def deltaRootFamilyCompletedModPH0Equiv
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : ∀ T : Finset σ, Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T))
    (hg₁ : ∀ T : Finset σ,
      Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
        (p : DeltaAdjoinDivision E (p : P)
          (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) →
      Function.Injective (WittVector.ghostMap :
        WittVector p (RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η) →
        ℕ → RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ)) :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} QA) 0).obj
      (((boundedAboveDerivedBaseChange qA).obj
          ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)))).obj)) ≃ₗ[QA]
      (B ⧸ Ideal.span {(p : B)}) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let e := DerivedCategory.Minus.ι.mapIso
    (deltaRootFamilyRelativeCompletedDerivedModPIso D b hpA w hw hg₀ hg₁ hg)
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} QA) 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} QA) 0).app
      (ModuleCat.of QA (B ⧸ Ideal.span {(p : B)}))).toLinearEquiv

/-- この実p還元は全ての非零次数で実ホモロジーが零。 -/
theorem deltaRootFamilyCompletedModP_homology_isZero
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : ∀ T : Finset σ, Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T))
    (hg₁ : ∀ T : Finset σ,
      Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
        (p : DeltaAdjoinDivision E (p : P)
          (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) →
      Function.Injective (WittVector.ghostMap :
        WittVector p (RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η) →
        ℕ → RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ)) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} QA) i).obj
      (((boundedAboveDerivedBaseChange qA).obj
          ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)))).obj)) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let e := (DerivedCategory.homologyFunctor (ModuleCat.{u} QA) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (deltaRootFamilyRelativeCompletedDerivedModPIso D b hpA w hw hg₀ hg₁ hg))
  exact IsZero.of_iso
    (derivedSingleHomology_isZero (ModuleCat.of QA (B ⧸ Ideal.span {(p : B)})) i hi) e

/-- 元のA上の実導来完備化をA→A/pで実還元したH0はA/p上忠実平坦。 -/
theorem deltaRootFamilyCompletedModPH0_moduleFaithfullyFlat
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : ∀ T : Finset σ, Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T))
    (hg₁ : ∀ T : Finset σ,
      Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
        (p : DeltaAdjoinDivision E (p : P)
          (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) →
      Function.Injective (WittVector.ghostMap :
        WittVector p (RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η) →
        ℕ → RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ)) :
    Module.FaithfullyFlat QA ((DerivedCategory.homologyFunctor (ModuleCat.{u} QA) 0).obj
      (((boundedAboveDerivedBaseChange qA).obj
          ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)))).obj)) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let := deltaRootRawModP_moduleFaithfullyFlat D b hpA hg w hw
  exact Module.FaithfullyFlat.of_linearEquiv QA (B ⧸ Ideal.span {(p : B)})
    (deltaRootFamilyCompletedModPH0Equiv D b hpA w hw hg₀ hg₁ hg)

end SerrePositivity.BhattScholze

end DeltaRootFamilyCompletedModPFlat
