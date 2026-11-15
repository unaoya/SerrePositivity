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
def Andre.deltaDivisionFiniteResidueFamilyList {m : ℕ} (s : Fin m → σ) : ℕ → List R₀
  | 0 => List.ofFn fun i => q₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a (s i) 0)
  | N + 1 => deltaDivisionFiniteResidueFamilyList s N ++
      List.ofFn fun i => q₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a (s i) (N + 1))

/-- m根・δ深さNの連結列の長さはm(N+1)。 -/
theorem Andre.deltaDivisionFiniteResidueFamilyList_length {m : ℕ} (s : Fin m → σ) (N : ℕ) :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList D d a s N).length = m * (N + 1) := by
  induction N with
  | zero => simp [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList]
  | succ N ih =>
      simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList, List.length_append, List.length_ofFn, ih,
        Nat.mul_add, Nat.mul_one]

/-- 全列挙された有限根族の関係リストは、ちょうど深さN以下の全関係を含む。 -/
theorem Andre.deltaDivisionFiniteResidueFamilyList_mem {m : ℕ} (s : Fin m → σ)
    (hs : Function.Surjective s) (N : ℕ) (z : R₀) :
    z ∈ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList D d a s N ↔
      ∃ t : σ, ∃ k : ℕ, k ≤ N ∧ q₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a t k) = z := by
  induction N with
  | zero =>
      simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList, List.mem_ofFn]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨s i, 0, le_rfl, rfl⟩
      · rintro ⟨t, k, hk, rfl⟩
        have hk0 : k = 0 := by omega
        subst k
        obtain ⟨i, rfl⟩ := hs t
        exact ⟨i, rfl⟩
  | succ N ih =>
      simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList, List.mem_append, ih, List.mem_ofFn]
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
theorem Andre.deltaDivisionFiniteResidueFamilyList_ofList {m : ℕ} (s : Fin m → σ)
    (hs : Function.Surjective s) (N : ℕ) :
    Ideal.ofList (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList D d a s N) =
      (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a N).map q₀ := by
  unfold _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal
  rw [Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList_mem D d a s hs N]
  constructor
  · rintro ⟨t, k, hk, he⟩
    exact ⟨(t, ⟨k, by omega⟩), he⟩
  · rintro ⟨⟨t, k⟩, he⟩
    exact ⟨t, k.val, by omega, he⟩

/-- 初項族が弱正則なら、有限根族の全有限δ深さの実残余列は弱正則。 -/
theorem Andre.deltaDivisionFiniteResidueFamilyList_isWeaklyRegular {m : ℕ} (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (hpL : Function.Injective (fun z : L₀ => (p : L₀) * z))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (h0 : RingTheory.Sequence.IsWeaklyRegular R₀
      (List.ofFn fun i => q₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a (s i) 0))) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular R₀ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList D d a s N) := by
  induction N with
  | zero => exact h0
  | succ N ih =>
      rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList, RingTheory.Sequence.isWeaklyRegular_append_iff]
      refine ⟨ih, ?_⟩
      have hI : (Ideal.ofList (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList D d a s N) • ⊤ :
          Submodule R₀ R₀) = (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a N).map q₀ := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top,
          _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList_ofList D d a s s.surjective N]
      rw [hI]
      let e := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueQuotientEquiv D d a N
      let rs := List.ofFn fun i => q₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a (s i) (N + 1))
      have hr : RingTheory.Sequence.IsWeaklyRegular
          (L₀ ⧸ (B₀ ⊔ _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a N))
          (List.ofFn fun i => Ideal.Quotient.mk
            (B₀ ⊔ _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a N)
            (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a (s i) (N + 1))) := by
        cases N with
        | zero => exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstJetResidue_fin_isWeaklyRegular D d a v hv s s.injective
        | succ n =>
            exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNextJet_quotient_fin_isWeaklyRegular
              D hpA hpL hg d a v hv n s s.injective
      let f := e.toRingHom.comp
        (Ideal.Quotient.mk ((_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a N).map q₀))
      have he (t : L₀) : f (q₀ t) =
          Ideal.Quotient.mk (B₀ ⊔ _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a N) t :=
        _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueQuotientEquiv_mk D d a N t
      refine (e.toAddEquiv.isWeaklyRegular_congr (as := rs) (bs := rs.map f) ?_).mpr ?_
      · apply List.forall₂_map_right_iff.mpr
        apply List.forall₂_same.mpr
        intro r _ x
        change e (Ideal.Quotient.mk ((_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a N).map q₀) r * x) =
          f r * e x
        rw [map_mul]
        rfl
      · simpa only [rs, List.map_ofFn, Function.comp_def, he] using hr

/-- 有限根族の連結した全δ関係は、初項入力の下で実Koszul分解を与える。 -/
theorem Andre.deltaDivisionFiniteResidueFamilyList_isKoszulResolution {m : ℕ} (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (hpL : Function.Injective (fun z : L₀ => (p : L₀) * z))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (h0 : RingTheory.Sequence.IsWeaklyRegular R₀
      (List.ofFn fun i => q₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a (s i) 0))) (N : ℕ) :
    SerrePositivity.IsKoszulResolution
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList D d a s N).get := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa only [List.ofFn_get] using
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList_isWeaklyRegular D d a s hpA hpL hg v hv h0 N

local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "bRel" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) a
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}

/-- 元の根関係族については、係数のp正則性とδd単元だけで全有限δ深さが弱正則。 -/
theorem Andre.deltaRootFiniteResidueFamilyList_isWeaklyRegular {m : ℕ} (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (L₁ ⧸ K₁)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList E₁ (MvPolynomial.C d) bRel s N) := by
  have hpP : IsSMulRegular P₁ (p : P₁) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₁)
  have hpL : IsSMulRegular L₁ (p : L₁) := by
    simpa only [map_natCast] using hpP.of_flat (S := L₁)
  let vP := v.map (MvPolynomial.C : A →+* P₁).toMonoidHom
  have hvP : (vP : P₁) = (E₁).delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = _
    rw [hv, _root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure_delta_C]
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList_isWeaklyRegular E₁ (MvPolynomial.C d) bRel s
    hpP hpL (_root_.SerrePositivity.witt_ghostMap_injective_of_mul_prime_injective p L₁ hpL) vP hvP
    (_root_.SerrePositivity.BhattScholze.Andre.deltaRootFirstRelation_mod_pd_fin_isWeaklyRegular D d a s s.injective) N

/-- 元の有限根族の全有限δ深さの実mod(p,d)Koszul分解。 -/
theorem Andre.deltaRootFiniteResidueFamilyList_isKoszulResolution {m : ℕ} (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    SerrePositivity.IsKoszulResolution
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList E₁ (MvPolynomial.C d) bRel s N).get := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa only [List.ofFn_get] using
    _root_.SerrePositivity.BhattScholze.Andre.deltaRootFiniteResidueFamilyList_isWeaklyRegular D d a s hpA v hv N

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteFamilyResidueKoszul

/-! ## 有限根族の全深さ実評価列と源グラフの座標 -/

@[expose] public noncomputable section DeltaDivisionFiniteFamilyEvaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {σ : Type u}

/-- 有限根族のδ座標を、深さ0から順に列挙する。 -/
def Andre.deltaDivisionFiniteFamilyCoordinates {m : ℕ} (s : Fin m → σ) : ℕ → List (σ × ℕ)
  | 0 => List.ofFn fun i => (s i, 0)
  | N + 1 => deltaDivisionFiniteFamilyCoordinates s N ++ List.ofFn fun i => (s i, N + 1)

/-- 座標列は、ちょうど選択根族の深さN以下の座標を含む。 -/
theorem Andre.deltaDivisionFiniteFamilyCoordinates_mem {m : ℕ} (s : Fin m → σ)
    (N : ℕ) (z : σ × ℕ) :
    z ∈ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates s N ↔
      ∃ i : Fin m, ∃ k : ℕ, k ≤ N ∧ (s i, k) = z := by
  induction N with
  | zero =>
      simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates, List.mem_ofFn]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, 0, le_rfl, rfl⟩
      · rintro ⟨i, k, hk, rfl⟩
        have hk0 : k = 0 := by omega
        subst k
        exact ⟨i, rfl⟩
  | succ N ih =>
      simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates, List.mem_append, ih, List.mem_ofFn]
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
theorem Andre.deltaDivisionFiniteFamilyCoordinates_nodup {m : ℕ} (s : Fin m → σ)
    (hs : Function.Injective s) (N : ℕ) :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates s N).Nodup := by
  have hblock (k : ℕ) : (List.ofFn fun i => (s i, k)).Nodup :=
    List.nodup_ofFn_ofInjective (fun _ _ he => hs (congrArg Prod.fst he))
  induction N with
  | zero => exact hblock 0
  | succ N ih =>
      rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates, List.nodup_append]
      refine ⟨ih, hblock _, ?_⟩
      intro z hz w hz' hzw
      subst w
      obtain ⟨i, k, hk, he⟩ := (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates_mem s N z).mp hz
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
theorem Andre.deltaDivisionFiniteFamilyCoordinates_map_iterated {m : ℕ} (s : Fin m → σ) (N : ℕ) :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates s N).map
      (fun z => q₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a z.1 z.2)) =
        _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList D d a s N := by
  induction N with
  | zero => simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates, List.map_ofFn,
      Function.comp_def, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList]
  | succ N ih => simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates, List.map_append, ih,
      List.map_ofFn, Function.comp_def, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList]

/-- 全有限座標を同じ標準剰余射で実評価したリスト。 -/
def Andre.deltaDivisionFiniteEvaluationFamilyList {m : ℕ} (s : Fin m → σ) (N : ℕ) : List R₀ :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates s N).map
    (fun z => q₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation D d a z.1 z.2))

/-- 実評価リストも、元の実有限δ関係イデアルの像を生成する。 -/
theorem Andre.deltaDivisionFiniteEvaluationFamilyList_ofList {m : ℕ} (s : Fin m → σ)
    (hs : Function.Surjective s) (N : ℕ) :
    Ideal.ofList (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList D d a s N) =
      (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a N).map q₀ := by
  rw [← _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteEvaluationIdeal_eq]
  unfold _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteEvaluationIdeal
  rw [Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList, List.mem_map]
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨i, k, hk, rfl⟩ := (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates_mem s N w).mp hw
    exact ⟨(s i, ⟨k, by omega⟩), he⟩
  · rintro ⟨⟨t, k⟩, he⟩
    obtain ⟨i, rfl⟩ := hs t
    exact ⟨(s i, k.val), (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates_mem s N _).mpr
      ⟨i, k.val, by omega, rfl⟩, he⟩

/-- 全δ反復列が弱正則なら、同じ全深さの実評価列も弱正則。 -/
theorem Andre.deltaDivisionFiniteEvaluationFamilyList_isWeaklyRegular {m : ℕ} (s : Fin m ≃ σ)
    (hg : ∀ N, RingTheory.Sequence.IsWeaklyRegular R₀
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList D d a s N)) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular R₀
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList D d a s N) := by
  induction N with
  | zero =>
      simpa only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates,
        List.map_ofFn, Function.comp_def, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList,
        _root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation, _root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation,
        Function.iterate_zero_apply] using hg 0
  | succ N ih =>
      have hstep : _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList D d a s (N + 1) =
          _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList D d a s N ++
            List.ofFn fun i => q₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation D d a (s i) (N + 1)) := by
        simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates,
          List.map_append, List.map_ofFn, Function.comp_def]
      rw [hstep, RingTheory.Sequence.isWeaklyRegular_append_iff]
      refine ⟨ih, ?_⟩
      have hr := hg (N + 1)
      rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList,
        RingTheory.Sequence.isWeaklyRegular_append_iff] at hr
      have hIg : (Ideal.ofList (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList D d a s N) • ⊤ :
          Submodule R₀ R₀) = (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a N).map q₀ := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top,
          _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList_ofList D d a s s.surjective N]
      have hIe : (Ideal.ofList (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList D d a s N) • ⊤ :
          Submodule R₀ R₀) = (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a N).map q₀ := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top,
          _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList_ofList D d a s s.surjective N]
      rw [hIe]
      have hrg := hr.2
      rw [hIg] at hrg
      let J := (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a N).map q₀
      let qN := (Ideal.Quotient.mk J).comp q₀
      have hkill : _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a N ≤ RingHom.ker qN := by
        intro z hz
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem q₀ hz)
      have hrg' : RingTheory.Sequence.IsWeaklyRegular (R₀ ⧸ J)
          (List.ofFn fun i => qN (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a (s i) (N + 1))) := by
        simpa only [List.map_ofFn, Function.comp_def, Ideal.Quotient.algebraMap_eq,
            J, qN, RingHom.comp_apply] using
          (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R₀ ⧸ J) _ _).mpr hrg
      have hre := _root_.SerrePositivity.BhattScholze.deltaDivisionMappedNextEvaluation_fin_isWeaklyRegular D d a qN N hkill s hrg'
      exact (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R₀ ⧸ J) _ _).mp
        (by simpa only [List.map_ofFn, Function.comp_def, Ideal.Quotient.algebraMap_eq,
            J, qN, RingHom.comp_apply] using hre)

variable {m : ℕ} (s : Fin m ≃ σ) (N : ℕ)
local notation "cs" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N
local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "c₁" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) a
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₁" => Ideal.Quotient.mk K₁
local notation "α₁" => deltaDivisionSourceMap (σ := σ) E₁ (MvPolynomial.C d)

/-- 有限根族の全実座標に沿う評価関係は、実mod(p,d)Koszul分解を与える。 -/
theorem Andre.deltaRootFiniteResidueEvaluationFamily_isKoszulResolution
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (cs).length =>
      q₁ (_root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
        ((cs).get i).1 ((cs).get i).2)) := by
  let f : σ × ℕ → L₁ ⧸ K₁ := fun z =>
    q₁ (_root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁ z.1 z.2)
  change SerrePositivity.IsKoszulResolution (f ∘ (cs).get)
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [← List.map_ofFn, List.ofFn_get]
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList_isWeaklyRegular E₁ (MvPolynomial.C d) c₁ s
    (fun k => _root_.SerrePositivity.BhattScholze.Andre.deltaRootFiniteResidueFamilyList_isWeaklyRegular D d a s hpA v hv k) N

/-- 同じ全実座標の源グラフ商のTorは、実残余評価Koszulホモロジー。 -/
def Andre.deltaRootFiniteResidueEvaluationFamilySourceTorIso (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} ((q₁).comp α₁)).leftDerived i).obj
      (ModuleCat.of L₁ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionSourceFiniteCoordinateQuotient E₁ c₁ (cs).get)) ≅
      (SerrePositivity.koszulComplex (fun j : Fin (cs).length =>
        q₁ (_root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
          ((cs).get j).1 ((cs).get j).2))).homology (-(i : ℤ)) := by
  have e := SerrePositivity.torAlgKoszulIso ((q₁).comp α₁)
    (fun j : Fin (cs).length => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation E₁ c₁ ((cs).get j))
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraph_fin_isKoszulResolution E₁ c₁ (cs).get
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates_nodup s s.injective N).injective_get) i
  have he : ((q₁).comp α₁) ∘
      (fun j : Fin (cs).length => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation E₁ c₁ ((cs).get j)) =
      (fun j : Fin (cs).length => q₁ (_root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
        ((cs).get j).1 ((cs).get j).2)) := by
    funext j
    exact congrArg q₁ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraph_map E₁ (MvPolynomial.C d) c₁ ((cs).get j))
  rw [he] at e
  exact e

/-- 有限根族の全深さ源グラフ商の、実残余自由δ射に沿う正次数Torは零。 -/
theorem Andre.deltaRootFiniteResidueEvaluationFamilySource_tor_subsingleton
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg ((q₁).comp α₁) (i + 1)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionSourceFiniteCoordinateQuotient E₁ c₁ (cs).get)) := by
  have hr := _root_.SerrePositivity.BhattScholze.Andre.deltaRootFiniteResidueEvaluationFamily_isKoszulResolution D d a s N hpA v hv
  have hz := hr.isZero (-((i + 1 : ℕ) : ℤ)) (by omega)
  have ht := hz.of_iso (_root_.SerrePositivity.BhattScholze.Andre.deltaRootFiniteResidueEvaluationFamilySourceTorIso D d a s N (i + 1))
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
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (a : σ → A)
variable {m : ℕ} (s : Fin m ≃ σ)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => a
local notation "β₀" => deltaDivisionSourceEval D a₀
/-- 有限根族評価の深さ≤Nの具体的な源グラフ関係列。 -/
def Andre.deltaDivisionEvaluationSourceFamilyGraphPrefix (N : ℕ) :
    Fin (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N).length → P₀ :=
  fun i => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation D a
    ((_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N).get i)

/-- 有限根族の深さN以下の実源グラフ商。 -/
abbrev Andre.DeltaDivisionEvaluationSourceFamilyQuotient (N : ℕ) :=
  _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionSourceFiniteCoordinateQuotient D a
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N).get

local notation "K₀" => fun N : ℕ =>
  Ideal.span (Set.range (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyGraphPrefix (σ := σ) D a s N))
local notation "Q₀" => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionEvaluationSourceFamilyQuotient (σ := σ) D a s

private theorem Andre.evaluation_one (s : σ) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation D (1 : A) a₀ s n =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation D a₀ (s, n) := by
  have h := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraph_map D (1 : A) a₀ (s, n)
  rw [_root_.SerrePositivity.BhattScholze.deltaDivisionSourceMap_one] at h
  exact h.symm

/-- 実源有限グラフイデアルは、分母1の有限δ関係イデアル。 -/
theorem Andre.deltaDivisionEvaluationSourceFamilyIdeal_eq_one (N : ℕ) :
    K₀ N = _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D (1 : A) a₀ N := by
  rw [← _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteEvaluationIdeal_eq]
  change Ideal.span (Set.range (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyGraphPrefix D a s N)) =
    Ideal.span (Set.range fun z : σ × Fin (N + 1) =>
      _root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation D (1 : A) a₀ z.1 z.2.val)
  apply congrArg Ideal.span
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, k, hk, he⟩ :=
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates_mem (s : Fin m → σ) N _).mp
        (List.get_mem _ i)
    refine ⟨(s j, ⟨k, by omega⟩), ?_⟩
    change _root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation D 1 a (s j) k =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation D a _
    rw [← he]
    exact _root_.SerrePositivity.BhattScholze.Andre.evaluation_one D a (s j) k
  · rintro ⟨⟨t, k⟩, rfl⟩
    obtain ⟨j, rfl⟩ := s.surjective t
    have hm : (s j, k.val) ∈ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N :=
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates_mem (s : Fin m → σ) N _).mpr
        ⟨j, k.val, by omega, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    refine ⟨i, ?_⟩
    change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation D a _ = _
    rw [hi]
    exact (_root_.SerrePositivity.BhattScholze.Andre.evaluation_one D a (s j) k.val).symm

/-- 実源評価核は、実有限グラフイデアルの上限。 -/
theorem Andre.deltaDivisionEvaluationSourceEval_ker_eq_iSup_family : RingHom.ker β₀ = ⨆ N, K₀ N := by
  rw [← _root_.SerrePositivity.BhattScholze.deltaDivisionUnitDenominator_ideal, _root_.SerrePositivity.BhattScholze.deltaDivision_deltaClosure_eq_iSup_finiteRelations]
  congr 1
  funext N
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyIdeal_eq_one D a s N).symm

/-- 実源の有限グラフイデアルは深さについて単調。 -/
theorem Andre.deltaDivisionEvaluationSourceFamilyIdeal_mono : Monotone K₀ := by
  intro N M h
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyIdeal_eq_one,
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyIdeal_eq_one]
  exact _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal_mono D (1 : A) a₀ h

private theorem Andre.finite_le_ker (N : ℕ) : K₀ N ≤ RingHom.ker β₀ := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceEval_ker_eq_iSup_family D a s]
  exact le_iSup (fun M : ℕ => Ideal.span
    (Set.range (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyGraphPrefix (σ := σ) D a s M))) N

/-- 有限源商間の標準線形遷移射。 -/
def Andre.deltaDivisionEvaluationSourceFamilyTransition (N : ℕ) : Q₀ N →ₗ[P₀] Q₀ (N + 1) :=
  Submodule.mapQ (K₀ N) (K₀ (N + 1)) LinearMap.id
    (by exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyIdeal_mono D a s (Nat.le_succ N))

/-- 標準遷移射は元の源環の標準商元を保つ。 -/
theorem Andre.deltaDivisionEvaluationSourceFamilyTransition_mk (N : ℕ) (r : P₀) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyTransition D a s N (Ideal.Quotient.mk (K₀ N) r) =
      Ideal.Quotient.mk (K₀ (N + 1)) r :=
  Submodule.mapQ_apply _ _ _ r

/-- 実有限源商の具体的なP加群逐次図式。 -/
def Andre.deltaDivisionEvaluationSourceFamilyModuleDiagram : ℕ ⥤ ModuleCat.{u} P₀ :=
  Functor.ofSequence
    (fun N => ModuleCat.ofHom (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyTransition D a s N))

/-- 実源商図式の隣接射は、定義した標準商遷移射。 -/
theorem Andre.deltaDivisionEvaluationSourceFamilyModuleDiagram_map_succ (N : ℕ) :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s).map
        (homOfLE (Nat.le_succ N)) =
      ModuleCat.ofHom (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyTransition D a s N) :=
  Functor.ofSequence_map_homOfLE_succ _ N

/-- βにより有限源商から実評価環Aへ降下する標準線形射。 -/
def Andre.deltaDivisionEvaluationSourceFamilyEval (N : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
    Q₀ N →ₗ[P₀] A := by
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
  exact Submodule.liftQ (K₀ N) (Algebra.linearMap P₀ A) (by exact _root_.SerrePositivity.BhattScholze.Andre.finite_le_ker D a s N)

/-- 有限源評価射は標準商元をβの実値へ送る。 -/
theorem Andre.deltaDivisionEvaluationSourceFamilyEval_mk (N : ℕ) (r : P₀) :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyEval D a s N (Ideal.Quotient.mk (K₀ N) r) = β₀ r := by
  let := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
  exact Submodule.liftQ_apply _ _ r

/-- 実評価環Aを頂点とする、有限源商の標準余錐。 -/
def Andre.deltaDivisionEvaluationSourceFamilyEvalCocone :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
    Cocone (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s) := by
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
  exact
    { pt := ModuleCat.of P₀ A
      ι := NatTrans.ofSequence
        (fun N => ModuleCat.ofHom (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyEval D a s N))
        (by
          intro N
          rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyModuleDiagram_map_succ]
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
          change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyEval D a s (N + 1)
            (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyTransition D a s N (Ideal.Quotient.mk (K₀ N) r)) =
              _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyEval D a s N (Ideal.Quotient.mk (K₀ N) r)
          rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyTransition_mk,
            _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyEval_mk,
            _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyEval_mk]) }

private theorem Andre.cocone_mk_independent
    (c : Cocone (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s))
    (N : ℕ) (r : P₀) :
    (c.ι.app N).hom (Ideal.Quotient.mk (K₀ N) r) =
      (c.ι.app 0).hom (Ideal.Quotient.mk (K₀ 0) r) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have h := congrArg (fun f => f.hom (Ideal.Quotient.mk (K₀ N) r))
      (c.w (homOfLE (Nat.le_succ N)))
    rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyModuleDiagram_map_succ] at h
    change (c.ι.app (N + 1)).hom
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyTransition D a s N (Ideal.Quotient.mk (K₀ N) r)) = _ at h
    rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyTransition_mk] at h
    exact h.trans ih

private theorem Andre.cocone_base_ker
    (c : Cocone (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s)) :
    RingHom.ker β₀ ≤ LinearMap.ker ((c.ι.app 0).hom.comp (Submodule.mkQ (K₀ 0))) := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceEval_ker_eq_iSup_family D a s]
  apply iSup_le
  intro N r hr
  change (c.ι.app 0).hom (Ideal.Quotient.mk (K₀ 0) r) = 0
  rw [← _root_.SerrePositivity.BhattScholze.Andre.cocone_mk_independent D a s c N r, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-- 実評価環Aは、源有限グラフ商の標準逐次colimitである。 -/
def Andre.deltaDivisionEvaluationSourceFamilyEvalIsColimit :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
    IsColimit (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyEvalCocone (σ := σ) D a s) := by
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
  let b : P₀ →ₗ[P₀] A := Algebra.linearMap P₀ A
  let e := LinearMap.quotKerEquivOfSurjective b (_root_.SerrePositivity.BhattScholze.deltaDivisionSourceEval_surjective D a₀)
  let desc (c : Cocone (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s)) :
      A →ₗ[P₀] c.pt :=
    (Submodule.liftQ (LinearMap.ker b)
      ((c.ι.app 0).hom.comp (Submodule.mkQ (K₀ 0))) (by exact _root_.SerrePositivity.BhattScholze.Andre.cocone_base_ker D a s c)).comp
        e.symm.toLinearMap
  have hdesc (c : Cocone (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s))
      (r : P₀) :
      desc c (β₀ r) = (c.ι.app 0).hom (Ideal.Quotient.mk (K₀ 0) r) := by
    change Submodule.liftQ (LinearMap.ker b)
      ((c.ι.app 0).hom.comp (Submodule.mkQ (K₀ 0)))
        (by exact _root_.SerrePositivity.BhattScholze.Andre.cocone_base_ker D a s c) (e.symm (b r)) = _
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
          (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyEval D a s N (Ideal.Quotient.mk (K₀ N) r)) = _
        rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyEval_mk, hdesc]
        exact (_root_.SerrePositivity.BhattScholze.Andre.cocone_mk_independent D a s c N r).symm
      uniq := by
        intro c f hf
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        obtain ⟨r, rfl⟩ := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEval_surjective D a₀ z
        have h := congrArg (fun g => g.hom (Ideal.Quotient.mk (K₀ 0) r)) (hf 0)
        change f.hom
          (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyEval D a s 0 (Ideal.Quotient.mk (K₀ 0) r)) = _ at h
        rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyEval_mk] at h
        exact h.trans (hdesc c r).symm }

/-- 実圏論的colimitと、βで作用する実評価環Aとの標準比較同型。 -/
def Andre.deltaDivisionEvaluationSourceFamilyColimitEvalIso :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
    colimit (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s) ≅
      ModuleCat.of P₀ A := by
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
  exact (colimit.isColimit _).coconePointUniqueUpToIso
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyEvalIsColimit D a s)

/-- 標準colimit比較同型は、各有限商からの標準β評価射を保つ。 -/
theorem Andre.deltaDivisionEvaluationSourceFamilyColimitEvalIso_ι (N : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
    colimit.ι (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyModuleDiagram (σ := σ) D a s) N ≫
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyColimitEvalIso D a s).hom =
        ModuleCat.ofHom (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyEval D a s N) := by
  let := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamilyEvalIsColimit D a s) N

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
local notation "l" N => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList D d a (fun i => (s i : σ)) N
local notation "l'" N => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList F dB aB s N

/-- 元の初項正則性から、任意根族内の有限部分族の全有限δ深さの列が弱正則。 -/
theorem Andre.deltaDivisionFiniteSubfamilyResidueList_isWeaklyRegular
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (h0 : RingTheory.Sequence.IsWeaklyRegular Q
      (List.ofFn fun i => q (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a (s i : σ) 0))) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular Q (l N) := by
  let e0 := _root_.SerrePositivity.BhattScholze.relativeFreeSubsetSplitAlgEquiv (A := A) T
  let e : Q ≃+* Q' := Ideal.quotientEquiv I J e0.toRingEquiv (by
    change J = Ideal.map e0.toRingHom I
    exact (_root_.SerrePositivity.BhattScholze.relativeFreeSubsetSplitAlgEquiv_map_pd (p := p) T d).symm)
  have he (x : L) : e (q x) = q' (e0 x) := Ideal.quotientEquiv_mk _ _ _ _ x
  have hrel (t : T) (n : ℕ) :
      e (q (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a (t : σ) n)) =
        q' (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation F dB aB t n) := by
    rw [he]
    exact congrArg q' (_root_.SerrePositivity.BhattScholze.relativeFreeSubsetSplitAlgEquiv_iteratedRelation T D d a t n)
  have transport (rs : List Q) :
      RingTheory.Sequence.IsWeaklyRegular Q rs ↔
        RingTheory.Sequence.IsWeaklyRegular Q' (rs.map e) := by
    apply e.toAddEquiv.isWeaklyRegular_congr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    exact e.map_mul r x
  have h0' : RingTheory.Sequence.IsWeaklyRegular Q'
      (List.ofFn fun i => q' (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation F dB aB (s i) 0)) := by
    simpa only [List.map_ofFn, Function.comp_def, hrel] using (transport _).mp h0
  have hpB : IsSMulRegular B (p : B) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := B)
  have hpC : IsSMulRegular C (p : C) := by
    simpa only [map_natCast] using hpB.of_flat (S := C)
  let vB : Bˣ := v.map (MvPolynomial.C : A →+* B).toMonoidHom
  have hvB : (vB : B) = (F).delta dB := by
    change MvPolynomial.C (v : A) = (F).delta (MvPolynomial.C d)
    rw [_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure_delta_C, hv]
  have hN := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList_isWeaklyRegular F dB aB s hpB hpC
    (_root_.SerrePositivity.witt_ghostMap_injective_of_mul_prime_injective p C hpC) vB hvB h0' N
  apply (transport _).mpr
  have hlist : ∀ k : ℕ, (l k).map e = l' k := by
    intro k
    induction k with
    | zero => simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList, List.map_ofFn,
        Function.comp_def, hrel]
    | succ k ih => simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList, List.map_append,
        ih, List.map_ofFn, Function.comp_def, hrel]
  rw [hlist]
  exact hN

/-- 同じ任意根族内の有限部分族の連結関係列は、実残余Koszul分解を与える。 -/
theorem Andre.deltaDivisionFiniteSubfamilyResidueList_isKoszulResolution
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (h0 : RingTheory.Sequence.IsWeaklyRegular Q
      (List.ofFn fun i => q (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a (s i : σ) 0))) (N : ℕ) :
    SerrePositivity.IsKoszulResolution (l N).get := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa only [List.ofFn_get] using
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSubfamilyResidueList_isWeaklyRegular D d a T s hpA v hv h0 N

local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "c₁" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) a
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}

/-- 具体的な根関係では、任意根族内の有限部分族の初項入力も自動的に得られる。 -/
theorem Andre.deltaRootFiniteSubfamilyResidueList_isWeaklyRegular
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (L₁ ⧸ K₁)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList E₁ (MvPolynomial.C d) c₁
        (fun i => (s i : σ)) N) := by
  have hpP : IsSMulRegular P₁ (p : P₁) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₁)
  let vP := v.map (MvPolynomial.C : A →+* P₁).toMonoidHom
  have hvP : (vP : P₁) = (E₁).delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = _
    rw [hv, _root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure_delta_C]
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSubfamilyResidueList_isWeaklyRegular
    E₁ (MvPolynomial.C d) c₁ T s hpP vP hvP
    (_root_.SerrePositivity.BhattScholze.Andre.deltaRootFirstRelation_mod_pd_fin_isWeaklyRegular D d a
      (fun i => (s i : σ)) (Subtype.coe_injective.comp s.injective)) N

/-- 任意根族の有限部分族・全有限δ深さの実mod(p,d)Koszul分解。 -/
theorem Andre.deltaRootFiniteSubfamilyResidueList_isKoszulResolution
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    SerrePositivity.IsKoszulResolution
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList E₁ (MvPolynomial.C d) c₁
        (fun i => (s i : σ)) N).get := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa only [List.ofFn_get] using
    _root_.SerrePositivity.BhattScholze.Andre.deltaRootFiniteSubfamilyResidueList_isWeaklyRegular D d a T s hpA v hv N

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteSubfamilyRegular

/-! ## 任意根族内の有限部分族の実評価Koszul分解とTor消滅 -/

@[expose] public noncomputable section DeltaDivisionFiniteSubfamilyTor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
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
theorem Andre.relativeFreeSubsetSplitAlgEquiv_evaluationRelation (t : T) (n : ℕ) :
    e0 (_root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation D d a (t : σ) n) =
      _root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation F dB aB t n := by
  have hi (x : L) : ∀ k : ℕ, e0 ((E).delta^[k] x) = (G).delta^[k] (e0 x) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have h := _root_.SerrePositivity.BhattScholze.relativeFreeSubsetSplitAlgEquiv_isDeltaHom T D ((E).delta^[k] x)
      change e0 ((E).delta ((E).delta^[k] x)) = (G).delta (e0 ((E).delta^[k] x)) at h
      exact h.trans (congrArg (G).delta ih)
  unfold _root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation
  rw [map_sub, hi, hi]
  simp only [map_mul, _root_.SerrePositivity.BhattScholze.relativeFreeSubsetSplitAlgEquiv_C,
    _root_.SerrePositivity.BhattScholze.relativeFreeSubsetSplitAlgEquiv_X_mem]

variable {m : ℕ} (s : Fin m ≃ T)
local notation "I" => Ideal.span {(p : L), MvPolynomial.C d}
local notation "Q" => L ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "J" => Ideal.span {(p : C), MvPolynomial.C dB}
local notation "Q'" => C ⧸ J
local notation "q'" => Ideal.Quotient.mk J

/-- 任意根族内の有限部分族の全深さ実評価列も、同じ初項入力から弱正則。 -/
theorem Andre.deltaDivisionFiniteSubfamilyEvaluationList_isWeaklyRegular
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (h0 : RingTheory.Sequence.IsWeaklyRegular Q
      (List.ofFn fun i => q (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a (s i : σ) 0))) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular Q
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList D d a (fun i => (s i : σ)) N) := by
  let e : Q ≃+* Q' := Ideal.quotientEquiv I J (e0).toRingEquiv (by
    change J = Ideal.map (e0).toRingHom I
    exact (_root_.SerrePositivity.BhattScholze.relativeFreeSubsetSplitAlgEquiv_map_pd (p := p) T d).symm)
  have he (x : L) : e (q x) = q' (e0 x) := Ideal.quotientEquiv_mk _ _ _ _ x
  have hrel (t : T) (n : ℕ) :
      e (q (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a (t : σ) n)) =
        q' (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation F dB aB t n) := by
    rw [he]
    exact congrArg q' (_root_.SerrePositivity.BhattScholze.relativeFreeSubsetSplitAlgEquiv_iteratedRelation T D d a t n)
  have heval (t : T) (n : ℕ) :
      e (q (_root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation D d a (t : σ) n)) =
        q' (_root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation F dB aB t n) := by
    rw [he]
    exact congrArg q' (_root_.SerrePositivity.BhattScholze.Andre.relativeFreeSubsetSplitAlgEquiv_evaluationRelation T D d a t n)
  have transport (rs : List Q) :
      RingTheory.Sequence.IsWeaklyRegular Q rs ↔
        RingTheory.Sequence.IsWeaklyRegular Q' (rs.map e) := by
    apply e.toAddEquiv.isWeaklyRegular_congr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    exact e.map_mul r x
  have hlist : ∀ k : ℕ,
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList D d a (fun i => (s i : σ)) k).map e =
        _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList F dB aB s k := by
    intro k
    induction k with
    | zero => simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList, List.map_ofFn,
        Function.comp_def, hrel]
    | succ k ih => simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList, List.map_append,
        ih, List.map_ofFn, Function.comp_def, hrel]
  have hg (k : ℕ) : RingTheory.Sequence.IsWeaklyRegular Q'
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList F dB aB s k) := by
    rw [← hlist]
    exact (transport _).mp
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSubfamilyResidueList_isWeaklyRegular D d a T s hpA v hv h0 k)
  have hcoords : ∀ k : ℕ, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (fun i => (s i : σ)) k =
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (s : Fin m → T) k).map
        (fun z => ((z.1 : σ), z.2)) := by
    intro k
    induction k with
    | zero => simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates, List.map_ofFn, Function.comp_def]
    | succ k ih => simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates, ih, List.map_append,
        List.map_ofFn, Function.comp_def]
  apply (transport _).mpr
  have hm : (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList D d a (fun i => (s i : σ)) N).map e =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList F dB aB s N := by
    simp only [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList, hcoords, List.map_map,
      Function.comp_def, heval]
  rw [hm]
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList_isWeaklyRegular F dB aB s hg N

local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "c₁" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) a
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₁" => Ideal.Quotient.mk K₁
local notation "α₁" => deltaDivisionSourceMap (σ := σ) E₁ (MvPolynomial.C d)
local notation "cs" N => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (fun i => (s i : σ)) N

/-- 任意根族の有限部分族の実評価列は、元のmod(p,d)商上でKoszul分解を与える。 -/
theorem Andre.deltaRootFiniteSubfamilyEvaluation_isKoszulResolution (N : ℕ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (cs N).length =>
      q₁ (_root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
        ((cs N).get i).1 ((cs N).get i).2)) := by
  have hpP : IsSMulRegular P₁ (p : P₁) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₁)
  let vP := v.map (MvPolynomial.C : A →+* P₁).toMonoidHom
  have hvP : (vP : P₁) = (E₁).delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = _
    rw [hv, _root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure_delta_C]
  let f : σ × ℕ → L₁ ⧸ K₁ := fun z =>
    q₁ (_root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁ z.1 z.2)
  change SerrePositivity.IsKoszulResolution (f ∘ (cs N).get)
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [← List.map_ofFn, List.ofFn_get]
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteSubfamilyEvaluationList_isWeaklyRegular
    T E₁ (MvPolynomial.C d) c₁ s hpP vP hvP
    (_root_.SerrePositivity.BhattScholze.Andre.deltaRootFirstRelation_mod_pd_fin_isWeaklyRegular D d a
      (fun i => (s i : σ)) (Subtype.coe_injective.comp s.injective)) N

/-- 同じ有限部分族の実源グラフ商のTorと、実残余評価Koszulホモロジーの比較。 -/
def Andre.deltaRootFiniteSubfamilySourceTorIso (N i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} ((q₁).comp α₁)).leftDerived i).obj
      (ModuleCat.of L₁ (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionSourceFiniteCoordinateQuotient E₁ c₁ (cs N).get)) ≅
      (SerrePositivity.koszulComplex (fun j : Fin (cs N).length =>
        q₁ (_root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
          ((cs N).get j).1 ((cs N).get j).2))).homology (-(i : ℤ)) := by
  have e := SerrePositivity.torAlgKoszulIso ((q₁).comp α₁)
    (fun j : Fin (cs N).length => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation E₁ c₁ ((cs N).get j))
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraph_fin_isKoszulResolution E₁ c₁ (cs N).get
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates_nodup _
        (Subtype.coe_injective.comp s.injective) N).injective_get) i
  have he : ((q₁).comp α₁) ∘
      (fun j : Fin (cs N).length => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation E₁ c₁ ((cs N).get j)) =
      (fun j : Fin (cs N).length => q₁ (_root_.SerrePositivity.BhattScholze.deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) c₁
        ((cs N).get j).1 ((cs N).get j).2)) := by
    funext j
    exact congrArg q₁ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraph_map E₁ (MvPolynomial.C d) c₁ ((cs N).get j))
  rw [he] at e
  exact e

/-- 任意根族内の有限部分族・全有限δ深さの源グラフ商の正次数Torは零。 -/
theorem Andre.deltaRootFiniteSubfamilySource_tor_subsingleton (N : ℕ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg ((q₁).comp α₁) (i + 1)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionSourceFiniteCoordinateQuotient E₁ c₁ (cs N).get)) := by
  have hr := _root_.SerrePositivity.BhattScholze.Andre.deltaRootFiniteSubfamilyEvaluation_isKoszulResolution T D d a s N hpA v hv
  have hz := hr.isZero (-((i + 1 : ℕ) : ℤ)) (by omega)
  have ht := hz.of_iso (_root_.SerrePositivity.BhattScholze.Andre.deltaRootFiniteSubfamilySourceTorIso T D d a s N (i + 1))
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
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "β₀" => deltaDivisionSourceEval D a₀
local notation "K₀" => fun N : ℕ =>
  Ideal.span (Set.range (_root_.SerrePositivity.BhattScholze.Andre.deltaPDivisionSourceGraphPrefix (σ := σ) D y N))
local notation "Q₀" => _root_.SerrePositivity.BhattScholze.Andre.DeltaPDivisionSourceFiniteQuotient (σ := σ) D y

/-- 実源有限グラフイデアルは、分母1の有限δ関係イデアル。 -/
theorem Andre.deltaDivisionSourceFiniteIdeal_eq_one (N : ℕ) :
    K₀ N = _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D (1 : A) a₀ N :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteIdeal_eq_one D a₀ N

/-- 実源評価核は、実有限グラフイデアルの上限。 -/
theorem Andre.deltaDivisionSourceEval_ker_eq_iSup_finite : RingHom.ker β₀ = ⨆ N, K₀ N :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceEval_ker_eq_iSup_finite D a₀

/-- 実源の有限グラフイデアルは深さについて単調。 -/
theorem Andre.deltaDivisionSourceFiniteIdeal_mono : Monotone K₀ :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteIdeal_mono D a₀

/-- 評価環Aの源P代数構造は、実評価射βそのものから与える。 -/
@[instance_reducible] def Andre.deltaDivisionSourceEvalAlgebra : Algebra P₀ A :=
  _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra D a₀

/-- 有限源商間の標準線形遷移射。 -/
def Andre.deltaDivisionSourceFiniteTransition (N : ℕ) : Q₀ N →ₗ[P₀] Q₀ (N + 1) :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteTransition D a₀ N

/-- 標準遷移射は元の源環の標準商元を保つ。 -/
theorem Andre.deltaDivisionSourceFiniteTransition_mk (N : ℕ) (r : P₀) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceFiniteTransition D y N (Ideal.Quotient.mk (K₀ N) r) =
      Ideal.Quotient.mk (K₀ (N + 1)) r :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteTransition_mk D a₀ N r

/-- 実有限源商の具体的なP加群逐次図式。 -/
def Andre.deltaDivisionSourceFiniteModuleDiagram : ℕ ⥤ ModuleCat.{u} P₀ :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteModuleDiagram D a₀

/-- 実源商図式の隣接射は、定義した標準商遷移射。 -/
theorem Andre.deltaDivisionSourceFiniteModuleDiagram_map_succ (N : ℕ) :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y).map (homOfLE (Nat.le_succ N)) =
      ModuleCat.ofHom (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceFiniteTransition D y N) :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteModuleDiagram_map_succ D a₀ N

/-- βにより有限源商から実評価環Aへ降下する標準線形射。 -/
def Andre.deltaDivisionSourceFiniteEval (N : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    Q₀ N →ₗ[P₀] A :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEval D a₀ N

/-- 有限源評価射は標準商元をβの実値へ送る。 -/
theorem Andre.deltaDivisionSourceFiniteEval_mk (N : ℕ) (r : P₀) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceFiniteEval D y N (Ideal.Quotient.mk (K₀ N) r) = β₀ r :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEval_mk D a₀ N r

/-- 実評価環Aを頂点とする、有限源商の標準余錐。 -/
def Andre.deltaDivisionSourceFiniteEvalCocone :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    Cocone (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y) :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEvalCocone D a₀

/-- 実評価環Aは、源有限グラフ商の標準逐次colimitである。 -/
def Andre.deltaDivisionSourceFiniteEvalIsColimit :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    IsColimit (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceFiniteEvalCocone (σ := σ) D y) :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteEvalIsColimit D a₀

/-- 実圏論的colimitと、βで作用する実評価環Aとの標準比較同型。 -/
def Andre.deltaDivisionSourceFiniteColimitEvalIso :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    colimit (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y) ≅ ModuleCat.of P₀ A :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteColimitEvalIso D a₀

/-- 標準colimit比較同型は、各有限商からの標準β評価射を保つ。 -/
theorem Andre.deltaDivisionSourceFiniteColimitEvalIso_ι (N : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceEvalAlgebra (σ := σ) D y
    colimit.ι (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceFiniteModuleDiagram (σ := σ) D y) N ≫
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceFiniteColimitEvalIso D y).hom =
        ModuleCat.ofHom (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceFiniteEval D y N) :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFiniteColimitEvalIso_ι D a₀ N

end SerrePositivity.BhattScholze

end DeltaDivisionSourceFiniteColimit
