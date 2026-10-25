module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaPDivisionSecondRelationRegular
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionFiniteJetRegularity
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionSecondFinitePresentation

/-! # 一元p除算の全有限δ関係商のp正則性

単元δ(p)と既存Witt正規化のghost単射を明示する。
元族全体のCFF拡大・完備化後の平坦性とは区別する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀

/-- 一元p除算の深さ0イデアルは、最初の実関係の主イデアル。 -/
theorem deltaPDivisionFiniteStageIdeal_zero : I₀ 0 = Ideal.span {g₀ 0} := by
  unfold deltaDivisionFiniteRelationIdeal
  congr 1
  ext z
  constructor
  · rintro ⟨⟨s, n⟩, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    have hn : n = 0 := Fin.ext (by omega)
    subst s
    subst n
    exact Set.mem_singleton _
  · intro hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact ⟨((default : σ), 0), rfl⟩

/-- 一元の次の有限段は一つの実δ関係を追加して得られる。 -/
theorem deltaPDivisionFiniteStageIdeal_succ (N : ℕ) :
    I₀ (N + 1) = I₀ N ⊔ Ideal.span {g₀ (N + 1)} := by
  rw [deltaDivisionFiniteRelationIdeal_succ]
  congr 1
  congr 1
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    subst s
    exact Set.mem_singleton _
  · intro hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact ⟨(default : σ), rfl⟩

/-- 深さ1イデアルは、最初の実関係とその最初のδ像で生成される。 -/
theorem deltaPDivisionFiniteStageIdeal_one : I₀ 1 = Ideal.span {g₀ 0, g₀ 1} := by
  rw [deltaPDivisionFiniteStageIdeal_succ, deltaPDivisionFiniteStageIdeal_zero]
  exact (Ideal.span_insert (g₀ 0) {g₀ 1}).symm

/-- 有限段の通常商のmod pを、既存の実mod(p,d)商(d=p)へ移す二重商同型。 -/
def deltaPDivisionFiniteStageModPEquiv (N : ℕ) :
    ((L₀ ⧸ I₀ N) ⧸ Ideal.span {(p : L₀ ⧸ I₀ N)}) ≃+*
      (L₀ ⧸ (Ideal.span {(p : L₀), MvPolynomial.C (p : A)} ⊔ I₀ N)) := by
  have hbase : Ideal.span {(p : L₀), MvPolynomial.C (p : A)} = Ideal.span {(p : L₀)} := by
    rw [map_natCast (MvPolynomial.C : A →+* L₀) p]
    exact congrArg Ideal.span (Set.insert_eq_of_mem (Set.mem_singleton (p : L₀)))
  exact (Ideal.quotEquivOfEq (show Ideal.span {(p : L₀ ⧸ I₀ N)} =
      (Ideal.span {(p : L₀)}).map (Ideal.Quotient.mk (I₀ N)) from by
        rw [Ideal.map_span, Set.image_singleton, map_natCast (Ideal.Quotient.mk (I₀ N)) p])).trans
    ((DoubleQuot.quotQuotEquivQuotSup (I₀ N) (Ideal.span {(p : L₀)})).trans
      (Ideal.quotEquivOfEq ((sup_comm _ _).trans
        (congrArg (fun J : Ideal L₀ ↦ J ⊔ I₀ N) hbase.symm))))

omit [Unique σ] in
/-- 有限段の二重商比較は元の自由環の標準像を保つ。 -/
theorem deltaPDivisionFiniteStageModPEquiv_mk (N : ℕ) (f : L₀) :
    deltaPDivisionFiniteStageModPEquiv (σ := σ) D y N
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk (I₀ N) f)) = Ideal.Quotient.mk _ f := by
  rw [deltaPDivisionFiniteStageModPEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply]
  change (Ideal.quotEquivOfEq _)
    (DoubleQuot.quotQuotEquivQuotSup _ _ (DoubleQuot.quotQuotMk _ _ f)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]

variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
include hpA hg hv

/-- 次の実δ関係は、前段通常商のmod p上で正則。 -/
theorem deltaPDivisionFiniteStage_next_mod_p_isSMulRegular (N : ℕ) :
    IsSMulRegular ((L₀ ⧸ I₀ (N + 1)) ⧸ Ideal.span {(p : L₀ ⧸ I₀ (N + 1))})
      (Ideal.Quotient.mk (Ideal.span {(p : L₀ ⧸ I₀ (N + 1))})
        (Ideal.Quotient.mk (I₀ (N + 1)) (g₀ (N + 2)))) := by
  have hpL : Function.Injective (fun x : L₀ ↦ (p : L₀) * x) := by
    have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
    have h' : IsSMulRegular L₀ (p : L₀) := by simpa only [map_natCast] using h
    intro x z hxz
    apply h'
    simpa only [smul_eq_mul] using hxz
  have hr := deltaDivisionFiniteNextJet_quotient_isSMulRegular
    D hpA hpL hg (p : A) a₀ v hv N (default : σ)
  let e := deltaPDivisionFiniteStageModPEquiv (σ := σ) D y (N + 1)
  have he : e (Ideal.Quotient.mk (Ideal.span {(p : L₀ ⧸ I₀ (N + 1))})
      (Ideal.Quotient.mk (I₀ (N + 1)) (g₀ (N + 2)))) =
      Ideal.Quotient.mk _ (g₀ (N + 2)) := deltaPDivisionFiniteStageModPEquiv_mk (σ := σ) D y _ _
  intro x z hxz
  apply e.injective
  apply hr
  have h := congrArg e hxz
  simpa only [smul_eq_mul, map_mul, he] using h

/-- 一元p除算のすべての有限実関係商はp正則。
単元δ(p)とghost単射は中間入力として明示する。 -/
theorem deltaPDivisionFiniteStage_quotient_p_mul_injective
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    Function.Injective (fun x : L₀ ⧸ I₀ N ↦ (p : L₀ ⧸ I₀ N) * x) := by
  have transport (J K : Ideal L₀) (hJK : J = K)
      (hK : IsSMulRegular (L₀ ⧸ K) (p : L₀ ⧸ K)) :
      IsSMulRegular (L₀ ⧸ J) (p : L₀ ⧸ J) := by
    subst K
    exact hK
  induction N using Nat.twoStepInduction with
  | zero =>
    exact transport _ _ (deltaPDivisionFiniteStageIdeal_zero (σ := σ) D y)
      (deltaPDivisionFirstRelation_quotient_p_mul_injective D
        (fun _ : σ ↦ y) (default : σ) hpA hy)
  | one =>
    exact transport _ _ (deltaPDivisionFiniteStageIdeal_one (σ := σ) D y)
      (deltaPDivisionSecondRelation_quotient_p_mul_injective D
        (fun _ : σ ↦ y) (default : σ) hpA hy)
  | more n _ ih =>
    let r := Ideal.Quotient.mk (I₀ (n + 1)) (g₀ (n + 2))
    have hr := SerrePositivity.isSMulRegular_quotient_span_of_regular_mod
      (L₀ ⧸ I₀ (n + 1)) (p : L₀ ⧸ I₀ (n + 1)) r ih
      (deltaPDivisionFiniteStage_next_mod_p_isSMulRegular (σ := σ) D y hpA hg v hv n)
    have hpQ : IsSMulRegular ((L₀ ⧸ I₀ (n + 1)) ⧸ Ideal.span {r})
        (p : (L₀ ⧸ I₀ (n + 1)) ⧸ Ideal.span {r}) :=
      Eq.mp (congrArg (fun c : (L₀ ⧸ I₀ (n + 1)) ⧸ Ideal.span {r} ↦
        IsSMulRegular ((L₀ ⧸ I₀ (n + 1)) ⧸ Ideal.span {r}) c)
          (map_natCast (Ideal.Quotient.mk (Ideal.span {r})) p)) hr
    let e : ((L₀ ⧸ I₀ (n + 1)) ⧸ Ideal.span {r}) ≃+* (L₀ ⧸ I₀ (n + 2)) :=
      (Ideal.quotEquivOfEq (show Ideal.span {r} =
        (Ideal.span {g₀ (n + 2)}).map (Ideal.Quotient.mk (I₀ (n + 1))) from by
          rw [Ideal.map_span, Set.image_singleton])).trans
        ((DoubleQuot.quotQuotEquivQuotSup (I₀ (n + 1)) (Ideal.span {g₀ (n + 2)})).trans
          (Ideal.quotEquivOfEq (deltaPDivisionFiniteStageIdeal_succ (σ := σ) D y (n + 1)).symm))
    intro x z hxz
    apply e.symm.injective
    apply hpQ
    have h := congrArg e.symm hxz
    simpa only [smul_eq_mul, map_mul, map_natCast] using h

end SerrePositivity.BhattScholze
