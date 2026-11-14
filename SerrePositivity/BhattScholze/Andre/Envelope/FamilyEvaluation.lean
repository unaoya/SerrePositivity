module

public import SerrePositivity.BhattScholze.Andre.Envelope.JetKoszul
public import SerrePositivity.BhattScholze.Andre.Envelope.JetRegularity
public import SerrePositivity.BhattScholze.Andre.Envelope.RootResidueKoszul
public import SerrePositivity.CommutativeAlgebra.Witt.Coefficients
public import SerrePositivity.BhattScholze.Delta.Division.Source
public import SerrePositivity.BhattScholze.Andre.Envelope.SourceEvaluation
public import Mathlib.CategoryTheory.Functor.OfSequence
public import SerrePositivity.BhattScholze.Andre.Envelope.PDivision

/-!
# 有限根族の評価と部分族の Tor

## 概要
源有限グラフ商の逐次極限、有限根添字に対する全 δ 深さの残余弱正則列、有限根族の全深さ評価列と源グラフの座標、有限根族評価の源有限グラフ商の逐次極限、任意根族の中の有限部分族の残余正則列・評価 Koszul 分解と Tor の消滅。
BS 著者版 Proposition 3.13 の完全平坦性に向けた、有限根族の評価関係の正則性と Tor の計算を与える。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/MonicCandidate`、`Envelope/PDivisionSource`、`Envelope/RootFamilySource`、`RootEnvelope/Source`、`Variants/Auxiliary`。
-/

universe u

/-! ## 有限根添字に対する全δ深さの実残余弱正則列 -/

@[expose] public noncomputable section DeltaDivisionFiniteFamilyResidueKoszul

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "B₀" => Ideal.span {(p : L₀), MvPolynomial.C d}
local notation "R₀" => L₀ ⧸ B₀
local notation "q₀" => Ideal.Quotient.mk B₀

/-- 有限根族の実残余関係を、δ深さの昇順に連結したリスト。 -/
def deltaDivisionFiniteResidueFamilyList {m : ℕ} (s : Fin m → σ) : ℕ → List R₀
  | 0 => List.ofFn fun i => q₀ (deltaDivisionIteratedRelation D d a (s i) 0)
  | N + 1 => deltaDivisionFiniteResidueFamilyList s N ++
      List.ofFn fun i => q₀ (deltaDivisionIteratedRelation D d a (s i) (N + 1))

/-- m根・δ深さNの連結列の長さはm(N+1)。 -/
theorem deltaDivisionFiniteResidueFamilyList_length {m : ℕ} (s : Fin m → σ) (N : ℕ) :
    (deltaDivisionFiniteResidueFamilyList D d a s N).length = m * (N + 1) := by
  induction N with
  | zero => simp [deltaDivisionFiniteResidueFamilyList]
  | succ N ih =>
      simp only [deltaDivisionFiniteResidueFamilyList, List.length_append, List.length_ofFn, ih,
        Nat.mul_add, Nat.mul_one]

/-- 全列挙された有限根族の関係リストは、ちょうど深さN以下の全関係を含む。 -/
theorem deltaDivisionFiniteResidueFamilyList_mem {m : ℕ} (s : Fin m → σ)
    (hs : Function.Surjective s) (N : ℕ) (z : R₀) :
    z ∈ deltaDivisionFiniteResidueFamilyList D d a s N ↔
      ∃ t : σ, ∃ k : ℕ, k ≤ N ∧ q₀ (deltaDivisionIteratedRelation D d a t k) = z := by
  induction N with
  | zero =>
      simp only [deltaDivisionFiniteResidueFamilyList, List.mem_ofFn]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨s i, 0, le_rfl, rfl⟩
      · rintro ⟨t, k, hk, rfl⟩
        have hk0 : k = 0 := by omega
        subst k
        obtain ⟨i, rfl⟩ := hs t
        exact ⟨i, rfl⟩
  | succ N ih =>
      simp only [deltaDivisionFiniteResidueFamilyList, List.mem_append, ih, List.mem_ofFn]
      constructor
      · rintro (⟨t, k, hk, he⟩ | ⟨i, he⟩)
        · exact ⟨t, k, by omega, he⟩
        · exact ⟨s i, N + 1, le_rfl, he⟩
      · rintro ⟨t, k, hk, he⟩
        by_cases h : k ≤ N
        · exact Or.inl ⟨t, k, h, he⟩
        · have heq : k = N + 1 := by omega
          subst k
          obtain ⟨i, rfl⟩ := hs t
          exact Or.inr ⟨i, he⟩

/-- 連結した関係リストのイデアルは、元の実有限δ関係イデアルの商像。 -/
theorem deltaDivisionFiniteResidueFamilyList_ofList {m : ℕ} (s : Fin m → σ)
    (hs : Function.Surjective s) (N : ℕ) :
    Ideal.ofList (deltaDivisionFiniteResidueFamilyList D d a s N) =
      (deltaDivisionFiniteRelationIdeal D d a N).map q₀ := by
  unfold deltaDivisionFiniteRelationIdeal
  rw [Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  rw [deltaDivisionFiniteResidueFamilyList_mem D d a s hs N]
  constructor
  · rintro ⟨t, k, hk, he⟩
    exact ⟨(t, ⟨k, by omega⟩), he⟩
  · rintro ⟨⟨t, k⟩, he⟩
    exact ⟨t, k.val, by omega, he⟩

/-- 初項族が弱正則なら、有限根族の全有限δ深さの実残余列は弱正則。 -/
theorem deltaDivisionFiniteResidueFamilyList_isWeaklyRegular {m : ℕ} (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (hpL : Function.Injective (fun z : L₀ => (p : L₀) * z))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (h0 : RingTheory.Sequence.IsWeaklyRegular R₀
      (List.ofFn fun i => q₀ (deltaDivisionIteratedRelation D d a (s i) 0))) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular R₀ (deltaDivisionFiniteResidueFamilyList D d a s N) := by
  induction N with
  | zero => exact h0
  | succ N ih =>
      rw [deltaDivisionFiniteResidueFamilyList, RingTheory.Sequence.isWeaklyRegular_append_iff]
      refine ⟨ih, ?_⟩
      have hI : (Ideal.ofList (deltaDivisionFiniteResidueFamilyList D d a s N) • ⊤ :
          Submodule R₀ R₀) = (deltaDivisionFiniteRelationIdeal D d a N).map q₀ := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top,
          deltaDivisionFiniteResidueFamilyList_ofList D d a s s.surjective N]
      rw [hI]
      let e := deltaDivisionFiniteResidueQuotientEquiv D d a N
      let rs := List.ofFn fun i => q₀ (deltaDivisionIteratedRelation D d a (s i) (N + 1))
      have hr : RingTheory.Sequence.IsWeaklyRegular
          (L₀ ⧸ (B₀ ⊔ deltaDivisionFiniteRelationIdeal D d a N))
          (List.ofFn fun i => Ideal.Quotient.mk
            (B₀ ⊔ deltaDivisionFiniteRelationIdeal D d a N)
            (deltaDivisionIteratedRelation D d a (s i) (N + 1))) := by
        cases N with
        | zero => exact deltaDivisionFirstJetResidue_fin_isWeaklyRegular D d a v hv s s.injective
        | succ n =>
            exact deltaDivisionFiniteNextJet_quotient_fin_isWeaklyRegular
              D hpA hpL hg d a v hv n s s.injective
      let f := e.toRingHom.comp
        (Ideal.Quotient.mk ((deltaDivisionFiniteRelationIdeal D d a N).map q₀))
      have he (t : L₀) : f (q₀ t) =
          Ideal.Quotient.mk (B₀ ⊔ deltaDivisionFiniteRelationIdeal D d a N) t :=
        deltaDivisionFiniteResidueQuotientEquiv_mk D d a N t
      refine (e.toAddEquiv.isWeaklyRegular_congr (as := rs) (bs := rs.map f) ?_).mpr ?_
      · apply List.forall₂_map_right_iff.mpr
        apply List.forall₂_same.mpr
        intro r _ x
        change e (Ideal.Quotient.mk ((deltaDivisionFiniteRelationIdeal D d a N).map q₀) r * x) =
          f r * e x
        rw [map_mul]
        rfl
      · simpa only [rs, List.map_ofFn, Function.comp_def, he] using hr

/-- 有限根族の連結した全δ関係は、初項入力の下で実Koszul分解を与える。 -/
theorem deltaDivisionFiniteResidueFamilyList_isKoszulResolution {m : ℕ} (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (hpL : Function.Injective (fun z : L₀ => (p : L₀) * z))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (h0 : RingTheory.Sequence.IsWeaklyRegular R₀
      (List.ofFn fun i => q₀ (deltaDivisionIteratedRelation D d a (s i) 0))) (N : ℕ) :
    SerrePositivity.IsKoszulResolution
      (deltaDivisionFiniteResidueFamilyList D d a s N).get := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa only [List.ofFn_get] using
    deltaDivisionFiniteResidueFamilyList_isWeaklyRegular D d a s hpA hpL hg v hv h0 N

local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "bRel" => deltaRootRelationFamily (p := p) a
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}

/-- 元の根関係族については、係数のp正則性とδd単元だけで全有限δ深さが弱正則。 -/
theorem deltaRootFiniteResidueFamilyList_isWeaklyRegular {m : ℕ} (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (L₁ ⧸ K₁)
      (deltaDivisionFiniteResidueFamilyList E₁ (MvPolynomial.C d) bRel s N) := by
  have hpP : IsSMulRegular P₁ (p : P₁) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₁)
  have hpL : IsSMulRegular L₁ (p : L₁) := by
    simpa only [map_natCast] using hpP.of_flat (S := L₁)
  let vP := v.map (MvPolynomial.C : A →+* P₁).toMonoidHom
  have hvP : (vP : P₁) = (E₁).delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = _
    rw [hv, polynomialRankOneDeltaStructure_delta_C]
  exact deltaDivisionFiniteResidueFamilyList_isWeaklyRegular E₁ (MvPolynomial.C d) bRel s
    hpP hpL (witt_ghostMap_injective_of_mul_prime_injective p L₁ hpL) vP hvP
    (deltaRootFirstRelation_mod_pd_fin_isWeaklyRegular D d a s s.injective) N

/-- 元の有限根族の全有限δ深さの実mod(p,d)Koszul分解。 -/
theorem deltaRootFiniteResidueFamilyList_isKoszulResolution {m : ℕ} (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    SerrePositivity.IsKoszulResolution
      (deltaDivisionFiniteResidueFamilyList E₁ (MvPolynomial.C d) bRel s N).get := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa only [List.ofFn_get] using
    deltaRootFiniteResidueFamilyList_isWeaklyRegular D d a s hpA v hv N

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteFamilyResidueKoszul

/-! ## 有限根族の全深さ実評価列と源グラフの座標 -/

@[expose] public noncomputable section DeltaDivisionFiniteFamilyEvaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {σ : Type u}

/-- 有限根族のδ座標を、深さ0から順に列挙する。 -/
def deltaDivisionFiniteFamilyCoordinates {m : ℕ} (s : Fin m → σ) : ℕ → List (σ × ℕ)
  | 0 => List.ofFn fun i => (s i, 0)
  | N + 1 => deltaDivisionFiniteFamilyCoordinates s N ++ List.ofFn fun i => (s i, N + 1)

/-- 座標列は、ちょうど選択根族の深さN以下の座標を含む。 -/
theorem deltaDivisionFiniteFamilyCoordinates_mem {m : ℕ} (s : Fin m → σ)
    (N : ℕ) (z : σ × ℕ) :
    z ∈ deltaDivisionFiniteFamilyCoordinates s N ↔
      ∃ i : Fin m, ∃ k : ℕ, k ≤ N ∧ (s i, k) = z := by
  induction N with
  | zero =>
      simp only [deltaDivisionFiniteFamilyCoordinates, List.mem_ofFn]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, 0, le_rfl, rfl⟩
      · rintro ⟨i, k, hk, rfl⟩
        have hk0 : k = 0 := by omega
        subst k
        exact ⟨i, rfl⟩
  | succ N ih =>
      simp only [deltaDivisionFiniteFamilyCoordinates, List.mem_append, ih, List.mem_ofFn]
      constructor
      · rintro (⟨i, k, hk, he⟩ | ⟨i, he⟩)
        · exact ⟨i, k, by omega, he⟩
        · exact ⟨i, N + 1, le_rfl, he⟩
      · rintro ⟨i, k, hk, he⟩
        by_cases h : k ≤ N
        · exact Or.inl ⟨i, k, h, he⟩
        · have heq : k = N + 1 := by omega
          subst k
          exact Or.inr ⟨i, he⟩

/-- 異なる根を選ぶと、全深さの座標列にも重複はない。 -/
theorem deltaDivisionFiniteFamilyCoordinates_nodup {m : ℕ} (s : Fin m → σ)
    (hs : Function.Injective s) (N : ℕ) :
    (deltaDivisionFiniteFamilyCoordinates s N).Nodup := by
  have hblock (k : ℕ) : (List.ofFn fun i => (s i, k)).Nodup :=
    List.nodup_ofFn_ofInjective (fun _ _ he => hs (congrArg Prod.fst he))
  induction N with
  | zero => exact hblock 0
  | succ N ih =>
      rw [deltaDivisionFiniteFamilyCoordinates, List.nodup_append]
      refine ⟨ih, hblock _, ?_⟩
      intro z hz w hz' hzw
      subst w
      obtain ⟨i, k, hk, he⟩ := (deltaDivisionFiniteFamilyCoordinates_mem s N z).mp hz
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hz'
      have h := congrArg Prod.snd (he.trans hj.symm)
      change k = N + 1 at h
      omega

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "B₀" => Ideal.span {(p : L₀), MvPolynomial.C d}
local notation "R₀" => L₀ ⧸ B₀
local notation "q₀" => Ideal.Quotient.mk B₀

/-- 同じ実座標列のδ反復関係像は、既存の全深さ実残余リスト。 -/
theorem deltaDivisionFiniteFamilyCoordinates_map_iterated {m : ℕ} (s : Fin m → σ) (N : ℕ) :
    (deltaDivisionFiniteFamilyCoordinates s N).map
      (fun z => q₀ (deltaDivisionIteratedRelation D d a z.1 z.2)) =
        deltaDivisionFiniteResidueFamilyList D d a s N := by
  induction N with
  | zero => simp only [deltaDivisionFiniteFamilyCoordinates, List.map_ofFn,
      Function.comp_def, deltaDivisionFiniteResidueFamilyList]
  | succ N ih => simp only [deltaDivisionFiniteFamilyCoordinates, List.map_append, ih,
      List.map_ofFn, Function.comp_def, deltaDivisionFiniteResidueFamilyList]

/-- 全有限座標を同じ標準剰余射で実評価したリスト。 -/
def deltaDivisionFiniteEvaluationFamilyList {m : ℕ} (s : Fin m → σ) (N : ℕ) : List R₀ :=
  (deltaDivisionFiniteFamilyCoordinates s N).map
    (fun z => q₀ (deltaDivisionEvaluationRelation D d a z.1 z.2))

/-- 実評価リストも、元の実有限δ関係イデアルの像を生成する。 -/
theorem deltaDivisionFiniteEvaluationFamilyList_ofList {m : ℕ} (s : Fin m → σ)
    (hs : Function.Surjective s) (N : ℕ) :
    Ideal.ofList (deltaDivisionFiniteEvaluationFamilyList D d a s N) =
      (deltaDivisionFiniteRelationIdeal D d a N).map q₀ := by
  rw [← deltaDivisionFiniteEvaluationIdeal_eq]
  unfold deltaDivisionFiniteEvaluationIdeal
  rw [Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  simp only [deltaDivisionFiniteEvaluationFamilyList, List.mem_map]
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨i, k, hk, rfl⟩ := (deltaDivisionFiniteFamilyCoordinates_mem s N w).mp hw
    exact ⟨(s i, ⟨k, by omega⟩), he⟩
  · rintro ⟨⟨t, k⟩, he⟩
    obtain ⟨i, rfl⟩ := hs t
    exact ⟨(s i, k.val), (deltaDivisionFiniteFamilyCoordinates_mem s N _).mpr
      ⟨i, k.val, by omega, rfl⟩, he⟩

/-- 全δ反復列が弱正則なら、同じ全深さの実評価列も弱正則。 -/
theorem deltaDivisionFiniteEvaluationFamilyList_isWeaklyRegular {m : ℕ} (s : Fin m ≃ σ)
    (hg : ∀ N, RingTheory.Sequence.IsWeaklyRegular R₀
      (deltaDivisionFiniteResidueFamilyList D d a s N)) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular R₀
      (deltaDivisionFiniteEvaluationFamilyList D d a s N) := by
  induction N with
  | zero =>
      simpa only [deltaDivisionFiniteEvaluationFamilyList, deltaDivisionFiniteFamilyCoordinates,
        List.map_ofFn, Function.comp_def, deltaDivisionFiniteResidueFamilyList,
        deltaDivisionEvaluationRelation, deltaDivisionIteratedRelation,
        Function.iterate_zero_apply] using hg 0
  | succ N ih =>
      have hstep : deltaDivisionFiniteEvaluationFamilyList D d a s (N + 1) =
          deltaDivisionFiniteEvaluationFamilyList D d a s N ++
            List.ofFn fun i => q₀ (deltaDivisionEvaluationRelation D d a (s i) (N + 1)) := by
        simp only [deltaDivisionFiniteEvaluationFamilyList, deltaDivisionFiniteFamilyCoordinates,
          List.map_append, List.map_ofFn, Function.comp_def]
      rw [hstep, RingTheory.Sequence.isWeaklyRegular_append_iff]
      refine ⟨ih, ?_⟩
      have hr := hg (N + 1)
      rw [deltaDivisionFiniteResidueFamilyList,
        RingTheory.Sequence.isWeaklyRegular_append_iff] at hr
      have hIg : (Ideal.ofList (deltaDivisionFiniteResidueFamilyList D d a s N) • ⊤ :
          Submodule R₀ R₀) = (deltaDivisionFiniteRelationIdeal D d a N).map q₀ := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top,
          deltaDivisionFiniteResidueFamilyList_ofList D d a s s.surjective N]
      have hIe : (Ideal.ofList (deltaDivisionFiniteEvaluationFamilyList D d a s N) • ⊤ :
          Submodule R₀ R₀) = (deltaDivisionFiniteRelationIdeal D d a N).map q₀ := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top,
          deltaDivisionFiniteEvaluationFamilyList_ofList D d a s s.surjective N]
      rw [hIe]
      have hrg := hr.2
      rw [hIg] at hrg
      let J := (deltaDivisionFiniteRelationIdeal D d a N).map q₀
      let qN := (Ideal.Quotient.mk J).comp q₀
      have hkill : deltaDivisionFiniteRelationIdeal D d a N ≤ RingHom.ker qN := by
        intro z hz
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem q₀ hz)
      have hrg' : RingTheory.Sequence.IsWeaklyRegular (R₀ ⧸ J)
          (List.ofFn fun i => qN (deltaDivisionIteratedRelation D d a (s i) (N + 1))) := by
        simpa only [List.map_ofFn, Function.comp_def, Ideal.Quotient.algebraMap_eq,
            J, qN, RingHom.comp_apply] using
          (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R₀ ⧸ J) _ _).mpr hrg
      have hre := deltaDivisionMappedNextEvaluation_fin_isWeaklyRegular D d a qN N hkill s hrg'
      exact (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R₀ ⧸ J) _ _).mp
        (by simpa only [List.map_ofFn, Function.comp_def, Ideal.Quotient.algebraMap_eq,
            J, qN, RingHom.comp_apply] using hre)

variable {m : ℕ} (s : Fin m ≃ σ) (N : ℕ)
local notation "cs" => deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N
local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "c₁" => deltaRootRelationFamily (p := p) a
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₁" => Ideal.Quotient.mk K₁
local notation "α₁" => deltaDivisionSourceMap (σ := σ) E₁ (MvPolynomial.C d)

/-- 有限根族の全実座標に沿う評価関係は、実mod(p,d)Koszul分解を与える。 -/
theorem deltaRootFiniteResidueEvaluationFamily_isKoszulResolution
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (cs).length =>
      q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
        ((cs).get i).1 ((cs).get i).2)) := by
  let f : σ × ℕ → L₁ ⧸ K₁ := fun z =>
    q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁ z.1 z.2)
  change SerrePositivity.IsKoszulResolution (f ∘ (cs).get)
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [← List.map_ofFn, List.ofFn_get]
  exact deltaDivisionFiniteEvaluationFamilyList_isWeaklyRegular E₁ (MvPolynomial.C d) c₁ s
    (fun k => deltaRootFiniteResidueFamilyList_isWeaklyRegular D d a s hpA v hv k) N

/-- 同じ全実座標の源グラフ商のTorは、実残余評価Koszulホモロジー。 -/
def deltaRootFiniteResidueEvaluationFamilySourceTorIso (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} ((q₁).comp α₁)).leftDerived i).obj
      (ModuleCat.of L₁ (DeltaDivisionSourceFiniteCoordinateQuotient E₁ c₁ (cs).get)) ≅
      (SerrePositivity.koszulComplex (fun j : Fin (cs).length =>
        q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
          ((cs).get j).1 ((cs).get j).2))).homology (-(i : ℤ)) := by
  have e := SerrePositivity.torAlgKoszulIso ((q₁).comp α₁)
    (fun j : Fin (cs).length => deltaDivisionSourceGraphRelation E₁ c₁ ((cs).get j))
    (deltaDivisionSourceGraph_fin_isKoszulResolution E₁ c₁ (cs).get
      (deltaDivisionFiniteFamilyCoordinates_nodup s s.injective N).injective_get) i
  have he : ((q₁).comp α₁) ∘
      (fun j : Fin (cs).length => deltaDivisionSourceGraphRelation E₁ c₁ ((cs).get j)) =
      (fun j : Fin (cs).length => q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
        ((cs).get j).1 ((cs).get j).2)) := by
    funext j
    exact congrArg q₁ (deltaDivisionSourceGraph_map E₁ (MvPolynomial.C d) c₁ ((cs).get j))
  rw [he] at e
  exact e

/-- 有限根族の全深さ源グラフ商の、実残余自由δ射に沿う正次数Torは零。 -/
theorem deltaRootFiniteResidueEvaluationFamilySource_tor_subsingleton
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg ((q₁).comp α₁) (i + 1)
      (DeltaDivisionSourceFiniteCoordinateQuotient E₁ c₁ (cs).get)) := by
  have hr := deltaRootFiniteResidueEvaluationFamily_isKoszulResolution D d a s N hpA v hv
  have hz := hr.isZero (-((i + 1 : ℕ) : ℤ)) (by omega)
  have ht := hz.of_iso (deltaRootFiniteResidueEvaluationFamilySourceTorIso D d a s N (i + 1))
  exact ModuleCat.subsingleton_of_isZero ht

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteFamilyEvaluation

/-! ## 有限根族評価の源有限グラフ商の標準逐次極限

源評価射βの核が有限グラフイデアルの上限であることから、実評価環Aへの標準余錐の普遍性を示す。
Torとcolimitの交換はここでは仮定も結論もしない。
-/

@[expose] public noncomputable section DeltaDivisionFamilySourceEvaluationColimit

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (a : σ → A)
variable {m : ℕ} (s : Fin m ≃ σ)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => a
local notation "β₀" => deltaDivisionSourceEval D a₀
/-- 有限根族評価の深さ≤Nの具体的な源グラフ関係列。 -/
def deltaDivisionEvaluationSourceFamilyGraphPrefix (N : ℕ) :
    Fin (deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N).length → P₀ :=
  fun i => deltaDivisionSourceGraphRelation D a
    ((deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N).get i)

/-- 有限根族の深さN以下の実源グラフ商。 -/
abbrev DeltaDivisionEvaluationSourceFamilyQuotient (N : ℕ) :=
  DeltaDivisionSourceFiniteCoordinateQuotient D a
    (deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N).get

local notation "K₀" => fun N : ℕ =>
  Ideal.span (Set.range (deltaDivisionEvaluationSourceFamilyGraphPrefix (σ := σ) D a s N))
local notation "Q₀" => DeltaDivisionEvaluationSourceFamilyQuotient (σ := σ) D a s

private theorem evaluation_one (s : σ) (n : ℕ) :
    deltaDivisionEvaluationRelation D (1 : A) a₀ s n =
      deltaDivisionSourceGraphRelation D a₀ (s, n) := by
  have h := deltaDivisionSourceGraph_map D (1 : A) a₀ (s, n)
  rw [deltaDivisionSourceMap_one] at h
  exact h.symm

/-- 実源有限グラフイデアルは、分母1の有限δ関係イデアル。 -/
theorem deltaDivisionEvaluationSourceFamilyIdeal_eq_one (N : ℕ) :
    K₀ N = deltaDivisionFiniteRelationIdeal D (1 : A) a₀ N := by
  rw [← deltaDivisionFiniteEvaluationIdeal_eq]
  change Ideal.span (Set.range (deltaDivisionEvaluationSourceFamilyGraphPrefix D a s N)) =
    Ideal.span (Set.range fun z : σ × Fin (N + 1) =>
      deltaDivisionEvaluationRelation D (1 : A) a₀ z.1 z.2.val)
  apply congrArg Ideal.span
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, k, hk, he⟩ :=
      (deltaDivisionFiniteFamilyCoordinates_mem (s : Fin m → σ) N _).mp
        (List.get_mem _ i)
    refine ⟨(s j, ⟨k, by omega⟩), ?_⟩
    change deltaDivisionEvaluationRelation D 1 a (s j) k =
      deltaDivisionSourceGraphRelation D a _
    rw [← he]
    exact evaluation_one D a (s j) k
  · rintro ⟨⟨t, k⟩, rfl⟩
    obtain ⟨j, rfl⟩ := s.surjective t
    have hm : (s j, k.val) ∈ deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N :=
      (deltaDivisionFiniteFamilyCoordinates_mem (s : Fin m → σ) N _).mpr
        ⟨j, k.val, by omega, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    refine ⟨i, ?_⟩
    change deltaDivisionSourceGraphRelation D a _ = _
    rw [hi]
    exact (evaluation_one D a (s j) k.val).symm

/-- 実源評価核は、実有限グラフイデアルの上限。 -/
theorem deltaDivisionEvaluationSourceEval_ker_eq_iSup_family : RingHom.ker β₀ = ⨆ N, K₀ N := by
  rw [← deltaDivisionUnitDenominator_ideal, deltaDivision_deltaClosure_eq_iSup_finiteRelations]
  congr 1
  funext N
  exact (deltaDivisionEvaluationSourceFamilyIdeal_eq_one D a s N).symm

/-- 実源の有限グラフイデアルは深さについて単調。 -/
theorem deltaDivisionEvaluationSourceFamilyIdeal_mono : Monotone K₀ := by
  intro N M h
  rw [deltaDivisionEvaluationSourceFamilyIdeal_eq_one,
    deltaDivisionEvaluationSourceFamilyIdeal_eq_one]
  exact deltaDivisionFiniteRelationIdeal_mono D (1 : A) a₀ h

private theorem finite_le_ker (N : ℕ) : K₀ N ≤ RingHom.ker β₀ := by
  rw [deltaDivisionEvaluationSourceEval_ker_eq_iSup_family D a s]
  exact le_iSup (fun M : ℕ => Ideal.span
    (Set.range (deltaDivisionEvaluationSourceFamilyGraphPrefix (σ := σ) D a s M))) N

/-- 有限源商間の標準線形遷移射。 -/
def deltaDivisionEvaluationSourceFamilyTransition (N : ℕ) : Q₀ N →ₗ[P₀] Q₀ (N + 1) :=
  Submodule.mapQ (K₀ N) (K₀ (N + 1)) LinearMap.id
    (by exact deltaDivisionEvaluationSourceFamilyIdeal_mono D a s (Nat.le_succ N))

/-- 標準遷移射は元の源環の標準商元を保つ。 -/
theorem deltaDivisionEvaluationSourceFamilyTransition_mk (N : ℕ) (r : P₀) :
    deltaDivisionEvaluationSourceFamilyTransition D a s N (Ideal.Quotient.mk (K₀ N) r) =
      Ideal.Quotient.mk (K₀ (N + 1)) r :=
  Submodule.mapQ_apply _ _ _ r

/-- 実有限源商の具体的なP加群逐次図式。 -/
def deltaDivisionEvaluationSourceFamilyModuleDiagram : ℕ ⥤ ModuleCat.{u} P₀ :=
  Functor.ofSequence
    (fun N => ModuleCat.ofHom (deltaDivisionEvaluationSourceFamilyTransition D a s N))

/-- 実源商図式の隣接射は、定義した標準商遷移射。 -/
theorem deltaDivisionEvaluationSourceFamilyModuleDiagram_map_succ (N : ℕ) :
    (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s).map
        (homOfLE (Nat.le_succ N)) =
      ModuleCat.ofHom (deltaDivisionEvaluationSourceFamilyTransition D a s N) :=
  Functor.ofSequence_map_homOfLE_succ _ N

/-- βにより有限源商から実評価環Aへ降下する標準線形射。 -/
def deltaDivisionEvaluationSourceFamilyEval (N : ℕ) :
    letI := deltaDivisionSourceEvaluationAlgebra D a₀
    Q₀ N →ₗ[P₀] A := by
  letI := deltaDivisionSourceEvaluationAlgebra D a₀
  exact Submodule.liftQ (K₀ N) (Algebra.linearMap P₀ A) (by exact finite_le_ker D a s N)

/-- 有限源評価射は標準商元をβの実値へ送る。 -/
theorem deltaDivisionEvaluationSourceFamilyEval_mk (N : ℕ) (r : P₀) :
    letI := deltaDivisionSourceEvaluationAlgebra D a₀
    deltaDivisionEvaluationSourceFamilyEval D a s N (Ideal.Quotient.mk (K₀ N) r) = β₀ r := by
  let := deltaDivisionSourceEvaluationAlgebra D a₀
  exact Submodule.liftQ_apply _ _ r

/-- 実評価環Aを頂点とする、有限源商の標準余錐。 -/
def deltaDivisionEvaluationSourceFamilyEvalCocone :
    letI := deltaDivisionSourceEvaluationAlgebra D a₀
    Cocone (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s) := by
  letI := deltaDivisionSourceEvaluationAlgebra D a₀
  exact
    { pt := ModuleCat.of P₀ A
      ι := NatTrans.ofSequence
        (fun N => ModuleCat.ofHom (deltaDivisionEvaluationSourceFamilyEval D a s N))
        (by
          intro N
          rw [deltaDivisionEvaluationSourceFamilyModuleDiagram_map_succ]
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
          change deltaDivisionEvaluationSourceFamilyEval D a s (N + 1)
            (deltaDivisionEvaluationSourceFamilyTransition D a s N (Ideal.Quotient.mk (K₀ N) r)) =
              deltaDivisionEvaluationSourceFamilyEval D a s N (Ideal.Quotient.mk (K₀ N) r)
          rw [deltaDivisionEvaluationSourceFamilyTransition_mk,
            deltaDivisionEvaluationSourceFamilyEval_mk,
            deltaDivisionEvaluationSourceFamilyEval_mk]) }

private theorem cocone_mk_independent
    (c : Cocone (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s))
    (N : ℕ) (r : P₀) :
    (c.ι.app N).hom (Ideal.Quotient.mk (K₀ N) r) =
      (c.ι.app 0).hom (Ideal.Quotient.mk (K₀ 0) r) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have h := congrArg (fun f => f.hom (Ideal.Quotient.mk (K₀ N) r))
      (c.w (homOfLE (Nat.le_succ N)))
    rw [deltaDivisionEvaluationSourceFamilyModuleDiagram_map_succ] at h
    change (c.ι.app (N + 1)).hom
      (deltaDivisionEvaluationSourceFamilyTransition D a s N (Ideal.Quotient.mk (K₀ N) r)) = _ at h
    rw [deltaDivisionEvaluationSourceFamilyTransition_mk] at h
    exact h.trans ih

private theorem cocone_base_ker
    (c : Cocone (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s)) :
    RingHom.ker β₀ ≤ LinearMap.ker ((c.ι.app 0).hom.comp (Submodule.mkQ (K₀ 0))) := by
  rw [deltaDivisionEvaluationSourceEval_ker_eq_iSup_family D a s]
  apply iSup_le
  intro N r hr
  change (c.ι.app 0).hom (Ideal.Quotient.mk (K₀ 0) r) = 0
  rw [← cocone_mk_independent D a s c N r, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-- 実評価環Aは、源有限グラフ商の標準逐次colimitである。 -/
def deltaDivisionEvaluationSourceFamilyEvalIsColimit :
    letI := deltaDivisionSourceEvaluationAlgebra D a₀
    IsColimit (deltaDivisionEvaluationSourceFamilyEvalCocone (σ := σ) D a s) := by
  letI := deltaDivisionSourceEvaluationAlgebra D a₀
  let b : P₀ →ₗ[P₀] A := Algebra.linearMap P₀ A
  let e := LinearMap.quotKerEquivOfSurjective b (deltaDivisionSourceEval_surjective D a₀)
  let desc (c : Cocone (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s)) :
      A →ₗ[P₀] c.pt :=
    (Submodule.liftQ (LinearMap.ker b)
      ((c.ι.app 0).hom.comp (Submodule.mkQ (K₀ 0))) (by exact cocone_base_ker D a s c)).comp
        e.symm.toLinearMap
  have hdesc (c : Cocone (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s))
      (r : P₀) :
      desc c (β₀ r) = (c.ι.app 0).hom (Ideal.Quotient.mk (K₀ 0) r) := by
    change Submodule.liftQ (LinearMap.ker b)
      ((c.ι.app 0).hom.comp (Submodule.mkQ (K₀ 0)))
        (by exact cocone_base_ker D a s c) (e.symm (b r)) = _
    dsimp only [e]
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  exact
    { desc := fun c => ModuleCat.ofHom (desc c)
      fac := by
        intro c N
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
        change desc c
          (deltaDivisionEvaluationSourceFamilyEval D a s N (Ideal.Quotient.mk (K₀ N) r)) = _
        rw [deltaDivisionEvaluationSourceFamilyEval_mk, hdesc]
        exact (cocone_mk_independent D a s c N r).symm
      uniq := by
        intro c f hf
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        obtain ⟨r, rfl⟩ := deltaDivisionSourceEval_surjective D a₀ z
        have h := congrArg (fun g => g.hom (Ideal.Quotient.mk (K₀ 0) r)) (hf 0)
        change f.hom
          (deltaDivisionEvaluationSourceFamilyEval D a s 0 (Ideal.Quotient.mk (K₀ 0) r)) = _ at h
        rw [deltaDivisionEvaluationSourceFamilyEval_mk] at h
        exact h.trans (hdesc c r).symm }

/-- 実圏論的colimitと、βで作用する実評価環Aとの標準比較同型。 -/
def deltaDivisionEvaluationSourceFamilyColimitEvalIso :
    letI := deltaDivisionSourceEvaluationAlgebra D a₀
    colimit (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s) ≅
      ModuleCat.of P₀ A := by
  letI := deltaDivisionSourceEvaluationAlgebra D a₀
  exact (colimit.isColimit _).coconePointUniqueUpToIso
    (deltaDivisionEvaluationSourceFamilyEvalIsColimit D a s)

/-- 標準colimit比較同型は、各有限商からの標準β評価射を保つ。 -/
theorem deltaDivisionEvaluationSourceFamilyColimitEvalIso_ι (N : ℕ) :
    letI := deltaDivisionSourceEvaluationAlgebra D a₀
    colimit.ι (deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s) N ≫
      (deltaDivisionEvaluationSourceFamilyColimitEvalIso D a s).hom =
        ModuleCat.ofHom (deltaDivisionEvaluationSourceFamilyEval D a s N) := by
  let := deltaDivisionSourceEvaluationAlgebra D a₀
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (deltaDivisionEvaluationSourceFamilyEvalIsColimit D a s) N

end SerrePositivity.BhattScholze

end DeltaDivisionFamilySourceEvaluationColimit

/-! ## 任意根族内の有限部分族の全深さ残余正則列 -/

@[expose] public noncomputable section DeltaDivisionFiniteSubfamilyRegular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (T : Set σ)
variable {m : ℕ} (s : Fin m ≃ T)
local notation "L" => RelativeFreeDeltaRing (R := A) σ
local notation "I" => Ideal.span {(p : L), MvPolynomial.C d}
local notation "Q" => L ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "B" => RelativeFreeDeltaRing (R := A) (Tᶜ : Set σ)
local notation "C" => RelativeFreeDeltaRing (R := B) T
local notation "F" => relativeFreeDeltaStructure (Tᶜ : Set σ) D
local notation "dB" => (MvPolynomial.C d : B)
local notation "aB" => fun t : T => (MvPolynomial.C (a t) : B)
local notation "J" => Ideal.span {(p : C), MvPolynomial.C dB}
local notation "Q'" => C ⧸ J
local notation "q'" => Ideal.Quotient.mk J
local notation "l" N => deltaDivisionFiniteResidueFamilyList D d a (fun i => (s i : σ)) N
local notation "l'" N => deltaDivisionFiniteResidueFamilyList F dB aB s N

/-- 元の初項正則性から、任意根族内の有限部分族の全有限δ深さの列が弱正則。 -/
theorem deltaDivisionFiniteSubfamilyResidueList_isWeaklyRegular
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (h0 : RingTheory.Sequence.IsWeaklyRegular Q
      (List.ofFn fun i => q (deltaDivisionIteratedRelation D d a (s i : σ) 0))) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular Q (l N) := by
  let e0 := relativeFreeSubsetSplitAlgEquiv (A := A) T
  let e : Q ≃+* Q' := Ideal.quotientEquiv I J e0.toRingEquiv (by
    change J = Ideal.map e0.toRingHom I
    exact (relativeFreeSubsetSplitAlgEquiv_map_pd (p := p) T d).symm)
  have he (x : L) : e (q x) = q' (e0 x) := Ideal.quotientEquiv_mk _ _ _ _ x
  have hrel (t : T) (n : ℕ) :
      e (q (deltaDivisionIteratedRelation D d a (t : σ) n)) =
        q' (deltaDivisionIteratedRelation F dB aB t n) := by
    rw [he]
    exact congrArg q' (relativeFreeSubsetSplitAlgEquiv_iteratedRelation T D d a t n)
  have transport (rs : List Q) :
      RingTheory.Sequence.IsWeaklyRegular Q rs ↔
        RingTheory.Sequence.IsWeaklyRegular Q' (rs.map e) := by
    apply e.toAddEquiv.isWeaklyRegular_congr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    exact e.map_mul r x
  have h0' : RingTheory.Sequence.IsWeaklyRegular Q'
      (List.ofFn fun i => q' (deltaDivisionIteratedRelation F dB aB (s i) 0)) := by
    simpa only [List.map_ofFn, Function.comp_def, hrel] using (transport _).mp h0
  have hpB : IsSMulRegular B (p : B) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := B)
  have hpC : IsSMulRegular C (p : C) := by
    simpa only [map_natCast] using hpB.of_flat (S := C)
  let vB : Bˣ := v.map (MvPolynomial.C : A →+* B).toMonoidHom
  have hvB : (vB : B) = (F).delta dB := by
    change MvPolynomial.C (v : A) = (F).delta (MvPolynomial.C d)
    rw [relativeFreeDeltaStructure_delta_C, hv]
  have hN := deltaDivisionFiniteResidueFamilyList_isWeaklyRegular F dB aB s hpB hpC
    (witt_ghostMap_injective_of_mul_prime_injective p C hpC) vB hvB h0' N
  apply (transport _).mpr
  have hlist : ∀ k : ℕ, (l k).map e = l' k := by
    intro k
    induction k with
    | zero => simp only [deltaDivisionFiniteResidueFamilyList, List.map_ofFn,
        Function.comp_def, hrel]
    | succ k ih => simp only [deltaDivisionFiniteResidueFamilyList, List.map_append,
        ih, List.map_ofFn, Function.comp_def, hrel]
  rw [hlist]
  exact hN

/-- 同じ任意根族内の有限部分族の連結関係列は、実残余Koszul分解を与える。 -/
theorem deltaDivisionFiniteSubfamilyResidueList_isKoszulResolution
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (h0 : RingTheory.Sequence.IsWeaklyRegular Q
      (List.ofFn fun i => q (deltaDivisionIteratedRelation D d a (s i : σ) 0))) (N : ℕ) :
    SerrePositivity.IsKoszulResolution (l N).get := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa only [List.ofFn_get] using
    deltaDivisionFiniteSubfamilyResidueList_isWeaklyRegular D d a T s hpA v hv h0 N

local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "c₁" => deltaRootRelationFamily (p := p) a
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}

/-- 具体的な根関係では、任意根族内の有限部分族の初項入力も自動的に得られる。 -/
theorem deltaRootFiniteSubfamilyResidueList_isWeaklyRegular
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (L₁ ⧸ K₁)
      (deltaDivisionFiniteResidueFamilyList E₁ (MvPolynomial.C d) c₁
        (fun i => (s i : σ)) N) := by
  have hpP : IsSMulRegular P₁ (p : P₁) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₁)
  let vP := v.map (MvPolynomial.C : A →+* P₁).toMonoidHom
  have hvP : (vP : P₁) = (E₁).delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = _
    rw [hv, polynomialRankOneDeltaStructure_delta_C]
  exact deltaDivisionFiniteSubfamilyResidueList_isWeaklyRegular
    E₁ (MvPolynomial.C d) c₁ T s hpP vP hvP
    (deltaRootFirstRelation_mod_pd_fin_isWeaklyRegular D d a
      (fun i => (s i : σ)) (Subtype.coe_injective.comp s.injective)) N

/-- 任意根族の有限部分族・全有限δ深さの実mod(p,d)Koszul分解。 -/
theorem deltaRootFiniteSubfamilyResidueList_isKoszulResolution
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    SerrePositivity.IsKoszulResolution
      (deltaDivisionFiniteResidueFamilyList E₁ (MvPolynomial.C d) c₁
        (fun i => (s i : σ)) N).get := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa only [List.ofFn_get] using
    deltaRootFiniteSubfamilyResidueList_isWeaklyRegular D d a T s hpA v hv N

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteSubfamilyRegular

/-! ## 任意根族内の有限部分族の実評価Koszul分解とTor消滅 -/

@[expose] public noncomputable section DeltaDivisionFiniteSubfamilyTor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (T : Set σ) (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L" => RelativeFreeDeltaRing (R := A) σ
local notation "E" => relativeFreeDeltaStructure σ D
local notation "B" => RelativeFreeDeltaRing (R := A) (Tᶜ : Set σ)
local notation "C" => RelativeFreeDeltaRing (R := B) T
local notation "F" => relativeFreeDeltaStructure (Tᶜ : Set σ) D
local notation "G" => relativeFreeDeltaStructure T F
local notation "dB" => (MvPolynomial.C d : B)
local notation "aB" => fun t : T => (MvPolynomial.C (a t) : B)
local notation "e0" => relativeFreeSubsetSplitAlgEquiv (A := A) T

/-- 部分族分離同型は、同じδ深さの実評価関係を保つ。 -/
theorem relativeFreeSubsetSplitAlgEquiv_evaluationRelation (t : T) (n : ℕ) :
    e0 (deltaDivisionEvaluationRelation D d a (t : σ) n) =
      deltaDivisionEvaluationRelation F dB aB t n := by
  have hi (x : L) : ∀ k : ℕ, e0 ((E).delta^[k] x) = (G).delta^[k] (e0 x) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have h := relativeFreeSubsetSplitAlgEquiv_isDeltaHom T D ((E).delta^[k] x)
      change e0 ((E).delta ((E).delta^[k] x)) = (G).delta (e0 ((E).delta^[k] x)) at h
      exact h.trans (congrArg (G).delta ih)
  unfold deltaDivisionEvaluationRelation
  rw [map_sub, hi, hi]
  simp only [map_mul, relativeFreeSubsetSplitAlgEquiv_C,
    relativeFreeSubsetSplitAlgEquiv_X_mem]

variable {m : ℕ} (s : Fin m ≃ T)
local notation "I" => Ideal.span {(p : L), MvPolynomial.C d}
local notation "Q" => L ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "J" => Ideal.span {(p : C), MvPolynomial.C dB}
local notation "Q'" => C ⧸ J
local notation "q'" => Ideal.Quotient.mk J

/-- 任意根族内の有限部分族の全深さ実評価列も、同じ初項入力から弱正則。 -/
theorem deltaDivisionFiniteSubfamilyEvaluationList_isWeaklyRegular
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (h0 : RingTheory.Sequence.IsWeaklyRegular Q
      (List.ofFn fun i => q (deltaDivisionIteratedRelation D d a (s i : σ) 0))) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular Q
      (deltaDivisionFiniteEvaluationFamilyList D d a (fun i => (s i : σ)) N) := by
  let e : Q ≃+* Q' := Ideal.quotientEquiv I J (e0).toRingEquiv (by
    change J = Ideal.map (e0).toRingHom I
    exact (relativeFreeSubsetSplitAlgEquiv_map_pd (p := p) T d).symm)
  have he (x : L) : e (q x) = q' (e0 x) := Ideal.quotientEquiv_mk _ _ _ _ x
  have hrel (t : T) (n : ℕ) :
      e (q (deltaDivisionIteratedRelation D d a (t : σ) n)) =
        q' (deltaDivisionIteratedRelation F dB aB t n) := by
    rw [he]
    exact congrArg q' (relativeFreeSubsetSplitAlgEquiv_iteratedRelation T D d a t n)
  have heval (t : T) (n : ℕ) :
      e (q (deltaDivisionEvaluationRelation D d a (t : σ) n)) =
        q' (deltaDivisionEvaluationRelation F dB aB t n) := by
    rw [he]
    exact congrArg q' (relativeFreeSubsetSplitAlgEquiv_evaluationRelation T D d a t n)
  have transport (rs : List Q) :
      RingTheory.Sequence.IsWeaklyRegular Q rs ↔
        RingTheory.Sequence.IsWeaklyRegular Q' (rs.map e) := by
    apply e.toAddEquiv.isWeaklyRegular_congr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    exact e.map_mul r x
  have hlist : ∀ k : ℕ,
      (deltaDivisionFiniteResidueFamilyList D d a (fun i => (s i : σ)) k).map e =
        deltaDivisionFiniteResidueFamilyList F dB aB s k := by
    intro k
    induction k with
    | zero => simp only [deltaDivisionFiniteResidueFamilyList, List.map_ofFn,
        Function.comp_def, hrel]
    | succ k ih => simp only [deltaDivisionFiniteResidueFamilyList, List.map_append,
        ih, List.map_ofFn, Function.comp_def, hrel]
  have hg (k : ℕ) : RingTheory.Sequence.IsWeaklyRegular Q'
      (deltaDivisionFiniteResidueFamilyList F dB aB s k) := by
    rw [← hlist]
    exact (transport _).mp
      (deltaDivisionFiniteSubfamilyResidueList_isWeaklyRegular D d a T s hpA v hv h0 k)
  have hcoords : ∀ k : ℕ, deltaDivisionFiniteFamilyCoordinates (fun i => (s i : σ)) k =
      (deltaDivisionFiniteFamilyCoordinates (s : Fin m → T) k).map
        (fun z => ((z.1 : σ), z.2)) := by
    intro k
    induction k with
    | zero => simp only [deltaDivisionFiniteFamilyCoordinates, List.map_ofFn, Function.comp_def]
    | succ k ih => simp only [deltaDivisionFiniteFamilyCoordinates, ih, List.map_append,
        List.map_ofFn, Function.comp_def]
  apply (transport _).mpr
  have hm : (deltaDivisionFiniteEvaluationFamilyList D d a (fun i => (s i : σ)) N).map e =
      deltaDivisionFiniteEvaluationFamilyList F dB aB s N := by
    simp only [deltaDivisionFiniteEvaluationFamilyList, hcoords, List.map_map,
      Function.comp_def, heval]
  rw [hm]
  exact deltaDivisionFiniteEvaluationFamilyList_isWeaklyRegular F dB aB s hg N

local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "c₁" => deltaRootRelationFamily (p := p) a
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₁" => Ideal.Quotient.mk K₁
local notation "α₁" => deltaDivisionSourceMap (σ := σ) E₁ (MvPolynomial.C d)
local notation "cs" N => deltaDivisionFiniteFamilyCoordinates (fun i => (s i : σ)) N

/-- 任意根族の有限部分族の実評価列は、元のmod(p,d)商上でKoszul分解を与える。 -/
theorem deltaRootFiniteSubfamilyEvaluation_isKoszulResolution (N : ℕ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (cs N).length =>
      q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
        ((cs N).get i).1 ((cs N).get i).2)) := by
  have hpP : IsSMulRegular P₁ (p : P₁) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₁)
  let vP := v.map (MvPolynomial.C : A →+* P₁).toMonoidHom
  have hvP : (vP : P₁) = (E₁).delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = _
    rw [hv, polynomialRankOneDeltaStructure_delta_C]
  let f : σ × ℕ → L₁ ⧸ K₁ := fun z =>
    q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁ z.1 z.2)
  change SerrePositivity.IsKoszulResolution (f ∘ (cs N).get)
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [← List.map_ofFn, List.ofFn_get]
  exact deltaDivisionFiniteSubfamilyEvaluationList_isWeaklyRegular
    T E₁ (MvPolynomial.C d) c₁ s hpP vP hvP
    (deltaRootFirstRelation_mod_pd_fin_isWeaklyRegular D d a
      (fun i => (s i : σ)) (Subtype.coe_injective.comp s.injective)) N

/-- 同じ有限部分族の実源グラフ商のTorと、実残余評価Koszulホモロジーの比較。 -/
def deltaRootFiniteSubfamilySourceTorIso (N i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} ((q₁).comp α₁)).leftDerived i).obj
      (ModuleCat.of L₁ (DeltaDivisionSourceFiniteCoordinateQuotient E₁ c₁ (cs N).get)) ≅
      (SerrePositivity.koszulComplex (fun j : Fin (cs N).length =>
        q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
          ((cs N).get j).1 ((cs N).get j).2))).homology (-(i : ℤ)) := by
  have e := SerrePositivity.torAlgKoszulIso ((q₁).comp α₁)
    (fun j : Fin (cs N).length => deltaDivisionSourceGraphRelation E₁ c₁ ((cs N).get j))
    (deltaDivisionSourceGraph_fin_isKoszulResolution E₁ c₁ (cs N).get
      (deltaDivisionFiniteFamilyCoordinates_nodup _
        (Subtype.coe_injective.comp s.injective) N).injective_get) i
  have he : ((q₁).comp α₁) ∘
      (fun j : Fin (cs N).length => deltaDivisionSourceGraphRelation E₁ c₁ ((cs N).get j)) =
      (fun j : Fin (cs N).length => q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
        ((cs N).get j).1 ((cs N).get j).2)) := by
    funext j
    exact congrArg q₁ (deltaDivisionSourceGraph_map E₁ (MvPolynomial.C d) c₁ ((cs N).get j))
  rw [he] at e
  exact e

/-- 任意根族内の有限部分族・全有限δ深さの源グラフ商の正次数Torは零。 -/
theorem deltaRootFiniteSubfamilySource_tor_subsingleton (N : ℕ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg ((q₁).comp α₁) (i + 1)
      (DeltaDivisionSourceFiniteCoordinateQuotient E₁ c₁ (cs N).get)) := by
  have hr := deltaRootFiniteSubfamilyEvaluation_isKoszulResolution T D d a s N hpA v hv
  have hz := hr.isZero (-((i + 1 : ℕ) : ℤ)) (by omega)
  have ht := hz.of_iso (deltaRootFiniteSubfamilySourceTorIso T D d a s N (i + 1))
  exact ModuleCat.subsingleton_of_isZero ht

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteSubfamilyTor

/-! ## 源有限グラフ商の標準逐次極限

源評価射βの核が有限グラフイデアルの上限であることから、実評価環Aへの標準余錐の普遍性を示す。
Torとcolimitの交換はここでは仮定も結論もしない。
-/

@[expose] public noncomputable section DeltaDivisionSourceFiniteColimit

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "β₀" => deltaDivisionSourceEval D a₀
local notation "K₀" => fun N : ℕ =>
  Ideal.span (Set.range (deltaPDivisionSourceGraphPrefix (σ := σ) D y N))
local notation "Q₀" => DeltaPDivisionSourceFiniteQuotient (σ := σ) D y

/-- 実源有限グラフイデアルは、分母1の有限δ関係イデアル。 -/
theorem deltaDivisionSourceFiniteIdeal_eq_one (N : ℕ) :
    K₀ N = deltaDivisionFiniteRelationIdeal D (1 : A) a₀ N :=
  deltaDivisionEvaluationSourceFiniteIdeal_eq_one D a₀ N

/-- 実源評価核は、実有限グラフイデアルの上限。 -/
theorem deltaDivisionSourceEval_ker_eq_iSup_finite : RingHom.ker β₀ = ⨆ N, K₀ N :=
  deltaDivisionEvaluationSourceEval_ker_eq_iSup_finite D a₀

/-- 実源の有限グラフイデアルは深さについて単調。 -/
theorem deltaDivisionSourceFiniteIdeal_mono : Monotone K₀ :=
  deltaDivisionEvaluationSourceFiniteIdeal_mono D a₀

/-- 評価環Aの源P代数構造は、実評価射βそのものから与える。 -/
@[instance_reducible] def deltaDivisionSourceEvalAlgebra : Algebra P₀ A :=
  deltaDivisionSourceEvaluationAlgebra D a₀

/-- 有限源商間の標準線形遷移射。 -/
def deltaDivisionSourceFiniteTransition (N : ℕ) : Q₀ N →ₗ[P₀] Q₀ (N + 1) :=
  deltaDivisionEvaluationSourceFiniteTransition D a₀ N

/-- 標準遷移射は元の源環の標準商元を保つ。 -/
theorem deltaDivisionSourceFiniteTransition_mk (N : ℕ) (r : P₀) :
    deltaDivisionSourceFiniteTransition D y N (Ideal.Quotient.mk (K₀ N) r) =
      Ideal.Quotient.mk (K₀ (N + 1)) r :=
  deltaDivisionEvaluationSourceFiniteTransition_mk D a₀ N r

/-- 実有限源商の具体的なP加群逐次図式。 -/
def deltaDivisionSourceFiniteModuleDiagram : ℕ ⥤ ModuleCat.{u} P₀ :=
  deltaDivisionEvaluationSourceFiniteModuleDiagram D a₀

/-- 実源商図式の隣接射は、定義した標準商遷移射。 -/
theorem deltaDivisionSourceFiniteModuleDiagram_map_succ (N : ℕ) :
    (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y).map (homOfLE (Nat.le_succ N)) =
      ModuleCat.ofHom (deltaDivisionSourceFiniteTransition D y N) :=
  deltaDivisionEvaluationSourceFiniteModuleDiagram_map_succ D a₀ N

/-- βにより有限源商から実評価環Aへ降下する標準線形射。 -/
def deltaDivisionSourceFiniteEval (N : ℕ) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    Q₀ N →ₗ[P₀] A :=
  deltaDivisionEvaluationSourceFiniteEval D a₀ N

/-- 有限源評価射は標準商元をβの実値へ送る。 -/
theorem deltaDivisionSourceFiniteEval_mk (N : ℕ) (r : P₀) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    deltaDivisionSourceFiniteEval D y N (Ideal.Quotient.mk (K₀ N) r) = β₀ r :=
  deltaDivisionEvaluationSourceFiniteEval_mk D a₀ N r

/-- 実評価環Aを頂点とする、有限源商の標準余錐。 -/
def deltaDivisionSourceFiniteEvalCocone :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    Cocone (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y) :=
  deltaDivisionEvaluationSourceFiniteEvalCocone D a₀

/-- 実評価環Aは、源有限グラフ商の標準逐次colimitである。 -/
def deltaDivisionSourceFiniteEvalIsColimit :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    IsColimit (deltaDivisionSourceFiniteEvalCocone (σ := σ) D y) :=
  deltaDivisionEvaluationSourceFiniteEvalIsColimit D a₀

/-- 実圏論的colimitと、βで作用する実評価環Aとの標準比較同型。 -/
def deltaDivisionSourceFiniteColimitEvalIso :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    colimit (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y) ≅ ModuleCat.of P₀ A :=
  deltaDivisionEvaluationSourceFiniteColimitEvalIso D a₀

/-- 標準colimit比較同型は、各有限商からの標準β評価射を保つ。 -/
theorem deltaDivisionSourceFiniteColimitEvalIso_ι (N : ℕ) :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    colimit.ι (deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y) N ≫
      (deltaDivisionSourceFiniteColimitEvalIso D y).hom =
        ModuleCat.ofHom (deltaDivisionSourceFiniteEval D y N) :=
  deltaDivisionEvaluationSourceFiniteColimitEvalIso_ι D a₀ N

end SerrePositivity.BhattScholze

end DeltaDivisionSourceFiniteColimit
