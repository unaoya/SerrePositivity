module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.RelativeFreeSubsetSplit
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionFiniteFamilyResidueKoszul
public import SerrePositivity.CommutativeAlgebra.WittGhostInjective

/-! # 任意根族内の有限部分族の全深さ残余正則列 -/

@[expose] public noncomputable section
universe u
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
