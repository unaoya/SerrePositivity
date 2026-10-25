module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionFiniteJetFamilyKoszul
public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionFirstJetResidueKoszul
public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootFirstResidueFamilyKoszul
public import SerrePositivity.CommutativeAlgebra.WittGhostInjective

/-! # 有限根添字に対する全δ深さの実残余弱正則列 -/

@[expose] public noncomputable section
universe u
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
