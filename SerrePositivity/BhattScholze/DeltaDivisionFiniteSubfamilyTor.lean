module

public import SerrePositivity.BhattScholze.DeltaDivisionFiniteSubfamilyRegular
public import SerrePositivity.BhattScholze.DeltaDivisionFiniteFamilyEvaluation

/-! # 任意根族内の有限部分族の実評価Koszul分解とTor消滅 -/

@[expose] public noncomputable section
universe u
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
