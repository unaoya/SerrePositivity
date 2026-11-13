module

public import SerrePositivity.BhattScholze.Delta.Division.Residue
public import SerrePositivity.BhattScholze.Andre.Envelope.RootRelation
public import SerrePositivity.BhattScholze.Andre.OrdinaryRoots.Adjoin
public import SerrePositivity.BhattScholze.Andre.Envelope.SourceEvaluation
public import SerrePositivity.BhattScholze.Delta.Division.Relations
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Mathlib.Logic.Equiv.Option
public import SerrePositivity.BhattScholze.Andre.Envelope.DivisionResidue

/-!
# δ 関係の正則性：最初の段と有限反復

## 概要
初期有限 δ 関係商の後続多項式表示、一般の除数の次の δ 関係・有限反復 δ 関係と評価関係の正則性、Frobenius 入力の次の p 除算入力、最初の δ 関係の mod (p,d) 正則性と Koszul 分解、環射に沿う Koszul 分解の移送。
BS 著者版 Proposition 3.13 の包を明示的な関係式で扱うため、δ 関係の有限反復で正則性を示す。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/FamilyEvaluation`、`Envelope/JetKoszul`、`Envelope/PDivision`、`Envelope/RootFamilyRaw`、`Envelope/RootResidueKoszul`、`PowerRootEnvelope/DeltaDivisionResidue`、`PowerRootEnvelope/DeltaDivisionWitt`、`PowerRootEnvelope/Unconditional/Residue`、`Variants/Auxiliary`。
-/

universe u v

/-! ## 最初のδ関係の一般mod(p,d)正則性

初期関係を課したmod(p,d)商を適切な係数商上の多項式環へ移す。
指定単元δdを使うが、正則性・ghost単射・完備性は追加仮定しない。
-/

@[expose] public noncomputable section DeltaDivisionFirstJetResidueRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "J₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a 0
local notation "K₀" => deltaDivisionFirstBaseIdeal (p := p) d a

/-- 全深さ0関係を課したmod(p,d)イデアルは、適切な係数イデアルの拡張。 -/
theorem deltaDivisionInitialResidueIdeal_eq_map :
    J₀ = (K₀).map (MvPolynomial.C : A →+* L₀) := by
  rw [deltaDivisionFirstBaseIdeal, Ideal.map_sup, Ideal.map_span, Ideal.map_span]
  simp only [Set.image_pair, map_natCast, ← Set.range_comp']
  apply le_antisymm
  · apply sup_le
    · exact le_sup_left
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨s, n⟩, rfl⟩
      have hn : n.val = 0 := by omega
      change deltaDivisionIteratedRelation D d a s n.val ∈ _
      rw [hn]
      change MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s) ∈ _
      apply Ideal.sub_mem
      · exact Ideal.mul_mem_right _ _
          ((show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ _ from le_sup_left)
            (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
      · exact (show Ideal.span (Set.range fun t => MvPolynomial.C (a t)) ≤ _ from le_sup_right)
          (Ideal.subset_span (Set.mem_range_self s))
  · apply sup_le
    · exact le_sup_left
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      have hg : deltaDivisionIteratedRelation D d a s 0 ∈ J₀ :=
        (show deltaDivisionFiniteRelationIdeal D d a 0 ≤ J₀ from le_sup_right)
          (Ideal.subset_span ⟨(s, 0), rfl⟩)
      have hd : MvPolynomial.C d ∈ J₀ :=
        (show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ J₀ from le_sup_left)
          (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      change MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s) ∈ J₀ at hg
      have h := (J₀).sub_mem ((J₀).mul_mem_right (MvPolynomial.X (s, 0)) hd) hg
      simpa only [sub_sub_cancel, SetLike.mem_coe] using h

/-- 初期mod(p,d)通常商の、適切な係数商上の多項式表示。 -/
def deltaDivisionInitialResiduePolynomialEquiv :
    (L₀ ⧸ J₀) ≃+* MvPolynomial (σ × ℕ) (A ⧸ K₀) :=
  (Ideal.quotEquivOfEq (deltaDivisionInitialResidueIdeal_eq_map D d a)).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial K₀).symm.toRingEquiv

/-- 初期mod(p,d)表示は実自由環の標準像と両立する。 -/
theorem deltaDivisionInitialResiduePolynomialEquiv_mk (f : L₀) :
    deltaDivisionInitialResiduePolynomialEquiv D d a (Ideal.Quotient.mk J₀ f) =
      MvPolynomial.map (Ideal.Quotient.mk K₀) f := by
  rw [deltaDivisionInitialResiduePolynomialEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact RingHom.congr_fun (monicPowerFamilyCoefficientQuotient_comp (σ × ℕ) A K₀) f

/-- 初期mod(p,d)商で、最初のδ関係は単元係数を持つ冪関係。 -/
theorem deltaDivisionFirstJet_residue (s : σ) :
    Ideal.Quotient.mk J₀ (deltaDivisionIteratedRelation D d a s 1) =
      Ideal.Quotient.mk J₀ (MvPolynomial.C (D.delta d)) *
        (Ideal.Quotient.mk J₀ (MvPolynomial.X (s, 0))) ^ p -
          Ideal.Quotient.mk J₀ (MvPolynomial.C (D.delta (a s))) := by
  let q := Ideal.Quotient.mk J₀
  have hp : q (p : L₀) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ J₀ from le_sup_left)
      (Ideal.subset_span (Set.mem_insert _ _)))
  have hd : q (MvPolynomial.C d) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ J₀ from le_sup_left)
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have ha : q (MvPolynomial.C (a s)) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [deltaDivisionInitialResidueIdeal_eq_map]
    exact Ideal.mem_map_of_mem _ ((show Ideal.span (Set.range a) ≤ K₀ from le_sup_right)
      (Ideal.subset_span (Set.mem_range_self s)))
  have h := deltaDivisionFirstRelation_delta_image (relativeFreeDeltaStructure σ D) q
    (MvPolynomial.C d) (MvPolynomial.X (s, 0)) (MvPolynomial.C (a s)) hp hd ha
  simpa only [deltaDivisionIteratedRelation, Function.iterate_one,
    relativeFreeDeltaStructure_delta_C] using h

/-- 初期係数商の多項式表示は、最初のδ関係を単元倍のモニック冪関係へ送る。 -/
theorem deltaDivisionFirstJet_residue_polynomial (v : Aˣ)
    (hv : (v : A) = D.delta d) (s : σ) :
    let Q := A ⧸ K₀
    let w := v.map (Ideal.Quotient.mk K₀).toMonoidHom
    deltaDivisionInitialResiduePolynomialEquiv D d a
      (Ideal.Quotient.mk J₀ (deltaDivisionIteratedRelation D d a s 1)) =
      MvPolynomial.C (w : Q) *
        (MvPolynomial.X (s, 0) ^ p -
          MvPolynomial.C (((w⁻¹ : Qˣ) : Q) * Ideal.Quotient.mk K₀ (D.delta (a s)))) := by
  let Q := A ⧸ K₀
  let w := v.map (Ideal.Quotient.mk K₀).toMonoidHom
  rw [deltaDivisionFirstJet_residue, map_sub, map_mul, map_pow,
    deltaDivisionInitialResiduePolynomialEquiv_mk,
    deltaDivisionInitialResiduePolynomialEquiv_mk,
    deltaDivisionInitialResiduePolynomialEquiv_mk,
    MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C, ← hv]
  change MvPolynomial.C (w : Q) * MvPolynomial.X (s, 0) ^ p -
    MvPolynomial.C (Ideal.Quotient.mk K₀ (D.delta (a s))) = _
  rw [mul_sub, ← MvPolynomial.C_mul, ← mul_assoc, Units.mul_inv, one_mul]

/-- δdが指定単元なら、最初のδ関係は全深さ0を課したmod(p,d)商上で非零因子。 -/
theorem deltaDivisionFirstJet_residue_isSMulRegular (v : Aˣ)
    (hv : (v : A) = D.delta d) (s : σ) :
    IsSMulRegular (L₀ ⧸ J₀)
      (Ideal.Quotient.mk J₀ (deltaDivisionIteratedRelation D d a s 1)) := by
  let e := deltaDivisionInitialResiduePolynomialEquiv D d a
  let Q := A ⧸ K₀
  let w := v.map (Ideal.Quotient.mk K₀).toMonoidHom
  have he := deltaDivisionFirstJet_residue_polynomial D d a v hv s
  change e (Ideal.Quotient.mk J₀ (deltaDivisionIteratedRelation D d a s 1)) = _ at he
  have hr := deltaRootRelation_isSMulRegular (p := p)
    (fun _ : σ × ℕ => ((w⁻¹ : Qˣ) : Q) * Ideal.Quotient.mk K₀ (D.delta (a s))) (s, 0)
  have hw : IsSMulRegular (MvPolynomial (σ × ℕ) Q) (MvPolynomial.C (w : Q)) :=
    (w.map (MvPolynomial.C : Q →+* MvPolynomial (σ × ℕ) Q).toMonoidHom).isSMulRegular _
  have hreg := hw.mul hr
  intro x y hxy
  apply e.injective
  apply hreg
  have h := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he, deltaRootRelationFamily] using h

end SerrePositivity.BhattScholze

end DeltaDivisionFirstJetResidueRegular

/-! ## 最初のδ関係の有限族のmod(p,d)Koszul分解

全深さ0を課した実mod(p,d)商上で、異なる有限個の深さ1関係を同時に扱う。
添字環の一元性・有限性やghost単射・完備性は要求しない。
-/

@[expose] public noncomputable section DeltaDivisionFirstJetResidueKoszul

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

private theorem unit_mul_list_regular {R : Type u} [CommRing R] (w : Rˣ) (l : List R)
    (h : RingTheory.Sequence.IsWeaklyRegular R l) :
    RingTheory.Sequence.IsWeaklyRegular R (l.map fun x => (w : R) * x) := by
  have hI (t : List R) : Ideal.ofList (t.map fun x => (w : R) * x) = Ideal.ofList t := by
    induction t with
    | nil => rfl
    | cons x t ih =>
        simp only [List.map_cons, Ideal.ofList_cons, ih,
          Ideal.span_singleton_mul_left_unit w.isUnit]
  constructor
  intro i hi
  have hi' : i < l.length := by simpa only [List.length_map] using hi
  rw [← List.map_take, hI, List.getElem_map]
  exact (w.isSMulRegular _).mul (h.regular_mod_prev i hi')

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "J₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a 0
local notation "K₀" => deltaDivisionFirstBaseIdeal (p := p) d a
local notation "f₀" => fun s : σ =>
  Ideal.Quotient.mk J₀ (deltaDivisionIteratedRelation D d a s 1)

/-- 指定単元δdに対し、異なる有限個の深さ1関係は実初期mod(p,d)商上で弱正則。 -/
theorem deltaDivisionFirstJetResidue_fin_isWeaklyRegular (hv : (v : A) = D.delta d)
    {m : ℕ} (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (L₀ ⧸ J₀) (List.ofFn fun i => f₀ (s i)) := by
  let Q := A ⧸ K₀
  let w₀ := v.map (Ideal.Quotient.mk K₀).toMonoidHom
  let w := w₀.map (MvPolynomial.C : Q →+* MvPolynomial (σ × ℕ) Q).toMonoidHom
  let c : σ × ℕ → Q := fun z => ((w₀⁻¹ : Qˣ) : Q) *
    Ideal.Quotient.mk K₀ (D.delta (a z.1))
  let e := deltaDivisionInitialResiduePolynomialEquiv D d a
  have hr := deltaRootRelation_fin_isWeaklyRegular (p := p) c
    (fun i => (s i, 0)) (fun _ _ hij => hs (congrArg Prod.fst hij))
  have hm := unit_mul_list_regular w _ hr
  have he (t : σ) : e (f₀ t) = (w : MvPolynomial (σ × ℕ) Q) *
      deltaRootRelationFamily (p := p) c (t, 0) := by
    exact deltaDivisionFirstJet_residue_polynomial D d a v hv t
  have hc := e.toAddEquiv.isWeaklyRegular_congr
    (as := List.ofFn fun i => f₀ (s i))
    (bs := (List.ofFn fun i => f₀ (s i)).map e)
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr (fun r _ x => by
      change e (r * x) = e r * e x
      exact map_mul e r x)))
  apply hc.mpr
  simpa only [List.map_ofFn, Function.comp_def, he] using hm

/-- 最初のδ関係の異なる有限族のKoszul複体は、実初期mod(p,d)商上の実通常商の分解。 -/
theorem deltaDivisionFirstJetResidue_fin_isKoszulResolution (hv : (v : A) = D.delta d)
    {m : ℕ} (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i => f₀ (s i)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaDivisionFirstJetResidue_fin_isWeaklyRegular D d a v hv s hs)

end SerrePositivity.BhattScholze

end DeltaDivisionFirstJetResidueKoszul

/-! ## 一般除数の有限反復δ関係と評価関係の正則性

全有限prefixの生成イデアルの一致を用いる。一元添字で任意除数・任意入力を扱い、
完備性・p正則性・ghost単射は要求しない。
-/

@[expose] public noncomputable section DeltaDivisionFiniteEvaluationRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]

/-- 次段評価イデアルは、前段に次の評価関係を追加したもの。 -/
theorem deltaDivisionFiniteEvaluationIdeal_succ
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ) :
    deltaDivisionFiniteEvaluationIdeal D d a (N + 1) =
      deltaDivisionFiniteEvaluationIdeal D d a N ⊔
        Ideal.span (Set.range fun s => deltaDivisionEvaluationRelation D d a s (N + 1)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    by_cases hi : i.val < N + 1
    · apply (show deltaDivisionFiniteEvaluationIdeal D d a N ≤
        deltaDivisionFiniteEvaluationIdeal D d a N ⊔ _ from le_sup_left)
      exact Ideal.subset_span ⟨(s, ⟨i.val, hi⟩), rfl⟩
    · have he : i.val = N + 1 := by omega
      change deltaDivisionEvaluationRelation D d a s i.val ∈ _
      rw [he]
      exact (show Ideal.span (Set.range fun t => deltaDivisionEvaluationRelation D d a t (N + 1)) ≤
        deltaDivisionFiniteEvaluationIdeal D d a N ⊔ _ from le_sup_right)
          (Ideal.subset_span (Set.mem_range_self s))
  · apply sup_le
    · rw [deltaDivisionFiniteEvaluationIdeal_eq, deltaDivisionFiniteEvaluationIdeal_eq]
      exact deltaDivisionFiniteRelationIdeal_mono D d a (Nat.le_succ N)
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      exact Ideal.subset_span ⟨(s, ⟨N + 1, Nat.lt_succ_self _⟩), rfl⟩

variable [Unique σ] (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "g₀" => deltaDivisionIteratedRelation D d a (default : σ)
local notation "h₀" => deltaDivisionEvaluationRelation D d a (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D d a

/-- 一元評価関係の全有限prefixの生成イデアルは既存の実I_N。 -/
theorem deltaDivisionFiniteEvaluation_ofList (N : ℕ) :
    Ideal.ofList (List.ofFn fun i : Fin (N + 1) => h₀ i.val) = I₀ N := by
  rw [← deltaDivisionFiniteEvaluationIdeal_eq]
  unfold Ideal.ofList deltaDivisionFiniteEvaluationIdeal
  congr 1
  ext z
  simp only [List.mem_ofFn, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(default, i), rfl⟩
  · rintro ⟨⟨s, i⟩, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    subst s
    exact ⟨i, rfl⟩

/-- 前段を消す任意通常環射の下で、次の実反復δ関係の正則性は実評価関係へ移る。 -/
theorem deltaDivisionFiniteEvaluation_next_isSMulRegular_map
    {T : Type v} [CommRing T] (q : L₀ →+* T) (N : ℕ)
    (hI : I₀ N ≤ RingHom.ker q) (hg : IsSMulRegular T (q (g₀ (N + 1)))) :
    IsSMulRegular T (q (h₀ (N + 1))) := by
  have he : I₀ (N + 1) = I₀ N ⊔ Ideal.span {h₀ (N + 1)} := by
    rw [← deltaDivisionFiniteEvaluationIdeal_eq D d a (N + 1),
      deltaDivisionFiniteEvaluationIdeal_succ, deltaDivisionFiniteEvaluationIdeal_eq]
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
      exact ⟨default, rfl⟩
  have hm : g₀ (N + 1) ∈ I₀ N ⊔ Ideal.span {h₀ (N + 1)} := by
    rw [← he]
    exact Ideal.subset_span ⟨(default, ⟨N + 1, Nat.lt_succ_self _⟩), rfl⟩
  obtain ⟨r, hr, t, ht, hrt⟩ := Submodule.mem_sup.mp hm
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ht
  have hdiv : q (g₀ (N + 1)) = q (h₀ (N + 1)) * q b := by
    rw [← hrt, map_add, (show q r = 0 from hI hr), zero_add, hb, map_mul]
  intro x z hxz
  apply hg
  change q (g₀ (N + 1)) * x = q (g₀ (N + 1)) * z
  change q (h₀ (N + 1)) * x = q (h₀ (N + 1)) * z at hxz
  calc
    q (g₀ (N + 1)) * x = q b * (q (h₀ (N + 1)) * x) := by rw [hdiv]; ring
    _ = q b * (q (h₀ (N + 1)) * z) := congrArg (fun w => q b * w) hxz
    _ = q (g₀ (N + 1)) * z := by rw [hdiv]; ring


/-- 前段商での次の反復差関係の非零因子性は、次の評価関係へ移る。 -/
theorem deltaDivisionFiniteEvaluation_next_isSMulRegular (N : ℕ)
    (hg : IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (g₀ (N + 1)))) :
    IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (h₀ (N + 1))) :=
  deltaDivisionFiniteEvaluation_next_isSMulRegular_map D d a (Ideal.Quotient.mk (I₀ N)) N
    (fun _ hr => Ideal.Quotient.eq_zero_iff_mem.mpr hr) hg

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteEvaluationRegular

/-! ## 通常環射後の有限δ列から実評価列へのKoszul分解の移送

対象環にδ構造を要求せず、各有限prefixの通常イデアルの一致を使う。
-/

@[expose] public noncomputable section DeltaDivisionMappedEvaluationKoszul

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
variable {T : Type v} [CommRing T] (q : RelativeFreeDeltaRing (R := A) σ →+* T)
local notation "g₀" => deltaDivisionIteratedRelation D d a (default : σ)
local notation "h₀" => deltaDivisionEvaluationRelation D d a (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D d a

/-- 通常射後の一元有限反復δ列の生成イデアルは、実有限関係イデアルの像。 -/
theorem deltaDivisionMappedIterated_ofList (N : ℕ) :
    Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q (g₀ i.val)) = (I₀ N).map q := by
  unfold deltaDivisionFiniteRelationIdeal
  rw [Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  ext z
  simp only [List.mem_ofFn, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(default, i), rfl⟩
  · rintro ⟨⟨s, i⟩, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    subst s
    exact ⟨i, rfl⟩

/-- 通常射後の一元有限評価列も、同じ実有限関係イデアルの像を生成する。 -/
theorem deltaDivisionMappedEvaluation_ofList (N : ℕ) :
    Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q (h₀ i.val)) = (I₀ N).map q := by
  rw [← deltaDivisionFiniteEvaluation_ofList D d a N, Ideal.map_ofList, List.map_ofFn,
    Function.comp_def]

/-- 全有限反復δ列が通常射後に弱正則なら、全有限実評価列も同じ環で弱正則。 -/
theorem deltaDivisionMappedEvaluation_isWeaklyRegular
    (hg : ∀ N : ℕ, RingTheory.Sequence.IsWeaklyRegular T
      (List.ofFn fun i : Fin (N + 1) => q (g₀ i.val))) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular T
      (List.ofFn fun i : Fin (N + 1) => q (h₀ i.val)) := by
  induction N with
  | zero =>
      simpa only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero, deltaDivisionIteratedRelation,
        deltaDivisionEvaluationRelation, Function.iterate_zero_apply] using hg 0
  | succ N ih =>
      rw [List.ofFn_succ', List.concat_eq_append,
        RingTheory.Sequence.isWeaklyRegular_append_iff]
      refine ⟨ih, ?_⟩
      rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      have hr := hg (N + 1)
      rw [List.ofFn_succ', List.concat_eq_append,
        RingTheory.Sequence.isWeaklyRegular_append_iff] at hr
      have hrg := hr.2
      rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hrg
      have hIg : (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q (g₀ i.val)) • ⊤ :
          Submodule T T) = (I₀ N).map q := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top, deltaDivisionMappedIterated_ofList]
      have hIh : (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q (h₀ i.val)) • ⊤ :
          Submodule T T) = (I₀ N).map q := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top, deltaDivisionMappedEvaluation_ofList]
      change IsSMulRegular (T ⧸
        (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q (g₀ i.val)) • ⊤ : Submodule T T))
        (q (g₀ (N + 1))) at hrg
      rw [hIg] at hrg
      change IsSMulRegular (T ⧸
        (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q (h₀ i.val)) • ⊤ : Submodule T T))
        (q (h₀ (N + 1)))
      rw [hIh]
      let qN := Ideal.Quotient.mk ((I₀ N).map q)
      have hkill : I₀ N ≤ RingHom.ker (qN.comp q) := by
        intro r hr
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem q hr)
      have hrg' : IsSMulRegular (T ⧸ (I₀ N).map q) ((qN.comp q) (g₀ (N + 1))) :=
        (isSMulRegular_map qN (fun _ => rfl)).mpr hrg
      exact (isSMulRegular_map qN (fun _ => rfl)).mp
        (deltaDivisionFiniteEvaluation_next_isSMulRegular_map D d a (qN.comp q) N hkill hrg')

/-- 通常環射後の全有限実評価Koszul複体は、全有限反復δ列の弱正則性から実分解となる。 -/
theorem deltaDivisionMappedEvaluation_isKoszulResolution
    (hg : ∀ N : ℕ, RingTheory.Sequence.IsWeaklyRegular T
      (List.ofFn fun i : Fin (N + 1) => q (g₀ i.val))) (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) => q (h₀ i.val)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaDivisionMappedEvaluation_isWeaklyRegular D d a q hg N)

end SerrePositivity.BhattScholze

end DeltaDivisionMappedEvaluationKoszul

/-! ## 初期有限δ関係商の後続多項式表示

実自由δ環上の通常商を、その関係が属する初期有限環の商と後続変数に分離する。
これは通常商の同型であり、導来δ基底変更の比較とは区別する。
-/

@[expose] public noncomputable section DeltaDivisionFiniteStageTailQuotient

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 任意の初期有限イデアルを拡張した自由環商は、初期商上の後続多項式環。 -/
def relativeFreeFiniteInitialQuotientEquiv (n : ℕ)
    (J : Ideal (MvPolynomial (σ × Fin n) A)) :
    (RelativeFreeDeltaRing (R := A) σ ⧸
      J.map (relativeFreeFiniteInitialPolynomialMap n σ A).toRingHom) ≃+*
      MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin n) A ⧸ J) := by
  let e := relativeFreeFiniteVariableSplitAlgEquiv n σ A
  have h : (J.map (relativeFreeFiniteInitialPolynomialMap n σ A).toRingHom).map
      e.toRingHom = J.map MvPolynomial.C := by
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro f
    exact relativeFreeFiniteVariableSplitAlgEquiv_initial n σ A f
  exact (Ideal.quotientEquiv _ _ e.toRingEquiv h.symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ × ℕ) J).symm.toRingEquiv

/-- この同型の標準商射上の式。 -/
theorem relativeFreeFiniteInitialQuotientEquiv_mk (n : ℕ)
    (J : Ideal (MvPolynomial (σ × Fin n) A)) (f : RelativeFreeDeltaRing (R := A) σ) :
    relativeFreeFiniteInitialQuotientEquiv n J (Ideal.Quotient.mk _ f) =
      MvPolynomial.map (Ideal.Quotient.mk J) (relativeFreeFiniteVariableSplitAlgEquiv n σ A f) := by
  rw [relativeFreeFiniteInitialQuotientEquiv, RingEquiv.trans_apply, Ideal.quotientEquiv_mk]
  exact RingHom.congr_fun (monicPowerFamilyCoefficientQuotient_comp
    (σ × ℕ) (MvPolynomial (σ × Fin n) A) J)
    (relativeFreeFiniteVariableSplitAlgEquiv n σ A f)

/-- 初期側の元の像は、初期商の係数となる。 -/
theorem relativeFreeFiniteInitialQuotientEquiv_initial (n : ℕ)
    (J : Ideal (MvPolynomial (σ × Fin n) A)) (f : MvPolynomial (σ × Fin n) A) :
    relativeFreeFiniteInitialQuotientEquiv n J
      (Ideal.Quotient.mk _ (relativeFreeFiniteInitialPolynomialMap n σ A f)) =
      MvPolynomial.C (Ideal.Quotient.mk J f) := by
  rw [relativeFreeFiniteInitialQuotientEquiv_mk,
    relativeFreeFiniteVariableSplitAlgEquiv_initial, MvPolynomial.map_C]

/-- 後続変数の像はそのまま外側変数となる。 -/
theorem relativeFreeFiniteInitialQuotientEquiv_tail (n : ℕ)
    (J : Ideal (MvPolynomial (σ × Fin n) A)) (s : σ) (k : ℕ) :
    relativeFreeFiniteInitialQuotientEquiv n J
      (Ideal.Quotient.mk _ (MvPolynomial.X (s, k + n))) = MvPolynomial.X (s, k) := by
  rw [relativeFreeFiniteInitialQuotientEquiv_mk,
    relativeFreeFiniteVariableSplitAlgEquiv_X_tail, MvPolynomial.map_X]

/-- 深さiの有限関係式を、固定した深さNの初期環へ含める。 -/
def deltaDivisionFiniteStageInitialRelation (D : DeltaStructure p A) (d : A) (a : σ → A)
    (N : ℕ) (s : σ) (i : Fin (N + 1)) : MvPolynomial (σ × Fin (N + 1)) A :=
  MvPolynomial.rename (fun z : σ × Fin (i.val + 1) =>
    (z.1, (⟨z.2.val, by omega⟩ : Fin (N + 1))))
      (deltaDivisionFiniteRelationPolynomial D d a s i.val)

/-- 固定初期環内に置いた関係の像は実際の反復δ関係。 -/
theorem deltaDivisionFiniteStageInitialRelation_image
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ) (s : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteInitialPolynomialMap (N + 1) σ A
      (deltaDivisionFiniteStageInitialRelation D d a N s i) =
        deltaDivisionIteratedRelation D d a s i.val := by
  rw [← deltaDivisionFiniteRelationPolynomial_image D d a s i.val]
  simp only [deltaDivisionFiniteStageInitialRelation, relativeFreeFiniteInitialPolynomialMap,
    MvPolynomial.rename_rename, Function.comp_def]

/-- 初期有限環内の全有限段関係イデアル。 -/
def deltaDivisionFiniteStageInitialIdeal (D : DeltaStructure p A) (d : A) (a : σ → A)
    (N : ℕ) : Ideal (MvPolynomial (σ × Fin (N + 1)) A) :=
  Ideal.span (Set.range fun z : σ × Fin (N + 1) =>
    deltaDivisionFiniteStageInitialRelation D d a N z.1 z.2)

/-- 初期関係イデアルの拡張は既存の実自由環上の有限関係イデアルに一致する。 -/
theorem deltaDivisionFiniteStageInitialIdeal_map
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ) :
    (deltaDivisionFiniteStageInitialIdeal D d a N).map
      (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom =
        deltaDivisionFiniteRelationIdeal D d a N := by
  simp only [deltaDivisionFiniteStageInitialIdeal, Ideal.map_span, ← Set.range_comp',
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    deltaDivisionFiniteStageInitialRelation_image, deltaDivisionFiniteRelationIdeal]

/-- 実有限関係商を初期関係商上の後続多項式環へ分離する。 -/
def deltaDivisionFiniteStageTailQuotientEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ) :
    (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFiniteRelationIdeal D d a N) ≃+*
      MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin (N + 1)) A ⧸
        deltaDivisionFiniteStageInitialIdeal D d a N) :=
  (Ideal.quotEquivOfEq (deltaDivisionFiniteStageInitialIdeal_map D d a N).symm).trans
    (relativeFreeFiniteInitialQuotientEquiv (N + 1) (deltaDivisionFiniteStageInitialIdeal D d a N))

/-- 実有限関係商の分離同型は標準商射と両立する。 -/
theorem deltaDivisionFiniteStageTailQuotientEquiv_mk
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ)
    (f : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionFiniteStageTailQuotientEquiv D d a N (Ideal.Quotient.mk _ f) =
      MvPolynomial.map (Ideal.Quotient.mk (deltaDivisionFiniteStageInitialIdeal D d a N))
        (relativeFreeFiniteVariableSplitAlgEquiv (N + 1) σ A f) := by
  rw [deltaDivisionFiniteStageTailQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, relativeFreeFiniteInitialQuotientEquiv_mk]

/-- 次の実δ関係は、分離後も最高変数の一次式。残りは初期商の係数。 -/
theorem deltaDivisionFiniteStageTailQuotientEquiv_next
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ) (s : σ) :
    deltaDivisionFiniteStageTailQuotientEquiv D d a N
      (Ideal.Quotient.mk _ (deltaDivisionIteratedRelation D d a s (N + 1))) =
        MvPolynomial.C (Ideal.Quotient.mk _ (MvPolynomial.C (D.frobeniusLift^[N + 1] d))) *
          MvPolynomial.X (s, 0) +
        MvPolynomial.C (Ideal.Quotient.mk _
          (deltaDivisionFiniteLeadingLowerPolynomial D d a s (N + 1))) := by
  rw [deltaDivisionFiniteStageTailQuotientEquiv_mk,
    deltaDivisionIteratedRelation_eq_leading_add_lower]
  have hx := relativeFreeFiniteVariableSplitAlgEquiv_X_tail (N + 1) σ A s 0
  simp only [zero_add] at hx
  rw [map_add, map_mul, relativeFreeFiniteVariableSplitAlgEquiv_C, hx,
    relativeFreeFiniteVariableSplitAlgEquiv_initial, map_add, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]

/-- 全自由環上の有限関係商のp正則性は、初期有限関係商へ降りる。 -/
theorem deltaDivisionFiniteStageInitialQuotient_p_mul_injective
    (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ)
    (hp : Function.Injective (fun x : RelativeFreeDeltaRing (R := A) σ ⧸
      deltaDivisionFiniteRelationIdeal D d a N => (p : _) * x)) :
    Function.Injective (fun x : MvPolynomial (σ × Fin (N + 1)) A ⧸
      deltaDivisionFiniteStageInitialIdeal D d a N => (p : _) * x) := by
  let B := MvPolynomial (σ × Fin (N + 1)) A ⧸ deltaDivisionFiniteStageInitialIdeal D d a N
  let e := deltaDivisionFiniteStageTailQuotientEquiv D d a N
  have hp' : Function.Injective (fun x : MvPolynomial (σ × ℕ) B => (p : _) * x) := by
    intro x y h
    apply e.symm.injective
    apply hp
    have he := congrArg e.symm h
    simpa only [map_mul, map_natCast] using he
  intro x y h
  apply (MvPolynomial.C_injective (σ := σ × ℕ))
  apply hp'
  have hC : (MvPolynomial.C : B →+* MvPolynomial (σ × ℕ) B) (p : B) = p :=
    map_natCast _ p
  simpa only [map_mul, hC] using
    congrArg (MvPolynomial.C : B →+* MvPolynomial (σ × ℕ) B) h

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteStageTailQuotient

/-! ## 一般除数の次δ関係の正則性

初期有限関係商と後続変数表示を用い、先頭係数φ^(N+1)(d)の正則性から
次の実反復δ関係の正則性を得る。完備性・ghost単射は要求しない。
-/

@[expose] public noncomputable section DeltaDivisionFiniteRelationsRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

private theorem linear_polynomial_regular {R : Type u} [CommRing R] (c b : R)
    (hc : Function.Injective (fun x : R => c * x)) :
    Function.Injective (fun x : Polynomial R =>
      (Polynomial.C c * Polynomial.X + Polynomial.C b) * x) := by
  nontriviality R
  have hc₀ : c ≠ 0 := by
    intro h
    have he : c * (1 : R) = c * 0 := by simp [h]
    exact one_ne_zero (hc he)
  have hp : (Polynomial.C c * Polynomial.X + Polynomial.C b) ∈
      nonZeroDivisors (Polynomial R) := by
    apply Polynomial.mem_nonZeroDivisors_of_leadingCoeff
    rw [Polynomial.leadingCoeff_linear hc₀]
    exact mem_nonZeroDivisors_iff_left.mpr fun x hx => hc (hx.trans (mul_zero c).symm)
  exact (isRegular_iff_mem_nonZeroDivisors.mpr hp).left

private theorem linear_mvpolynomial_regular {R : Type u} [CommRing R] {τ : Type v}
    (c b : R) (s : τ) (hc : Function.Injective (fun x : R => c * x)) :
    IsSMulRegular (MvPolynomial τ R) (MvPolynomial.C c * MvPolynomial.X s + MvPolynomial.C b) := by
  classical
  let e := (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe s).symm).trans
    (MvPolynomial.optionEquivLeft R {t : τ // t ≠ s})
  have he : e (MvPolynomial.C c * MvPolynomial.X s + MvPolynomial.C b) =
      Polynomial.C (MvPolynomial.C c) * Polynomial.X + Polynomial.C (MvPolynomial.C b) := by
    simp [e, MvPolynomial.renameEquiv]
  have hc' := (show IsSMulRegular R c from hc).of_flat
    (S := MvPolynomial {t : τ // t ≠ s} R)
  have hr := linear_polynomial_regular (MvPolynomial.C c) (MvPolynomial.C b) hc'
  intro x y h
  apply e.injective
  apply hr
  have hh := congrArg e h
  simpa only [smul_eq_mul, map_mul, he] using hh

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => deltaDivisionFiniteRelationIdeal D d a

/-- 除数dが正則なら、任意元の最初の実除算関係は自由δ環上で非零因子。 -/
theorem deltaDivisionFirstRelation_isSMulRegular (s : σ)
    (hd : IsSMulRegular A d) :
    IsSMulRegular L₀ (deltaDivisionIteratedRelation D d a s 0) := by
  change IsSMulRegular L₀ (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s))
  rw [sub_eq_add_neg, ← map_neg]
  exact linear_mvpolynomial_regular d (-(a s)) (s, 0) hd

/-- 前段商での先頭係数の正則性は、初期有限関係商の同じ係数へ降りる。 -/
theorem deltaDivisionFiniteStageInitialQuotient_coefficient_isSMulRegular (N : ℕ) (c : A)
    (hc : IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (MvPolynomial.C c))) :
    IsSMulRegular (MvPolynomial (σ × Fin (N + 1)) A ⧸
      deltaDivisionFiniteStageInitialIdeal D d a N)
      (Ideal.Quotient.mk (deltaDivisionFiniteStageInitialIdeal D d a N) (MvPolynomial.C c)) := by
  let J := deltaDivisionFiniteStageInitialIdeal D d a N
  let B := MvPolynomial (σ × Fin (N + 1)) A ⧸ J
  let e := deltaDivisionFiniteStageTailQuotientEquiv D d a N
  have he : e (Ideal.Quotient.mk (I₀ N) (MvPolynomial.C c)) =
      MvPolynomial.C (Ideal.Quotient.mk J (MvPolynomial.C c)) := by
    rw [deltaDivisionFiniteStageTailQuotientEquiv_mk,
      relativeFreeFiniteVariableSplitAlgEquiv_C, MvPolynomial.map_C]
  have hc' : IsSMulRegular (MvPolynomial (σ × ℕ) B)
      (MvPolynomial.C (σ := σ × ℕ) (Ideal.Quotient.mk J (MvPolynomial.C c))) := by
    intro x y h
    apply e.symm.injective
    apply hc
    apply e.injective
    simpa only [smul_eq_mul, map_mul, he, e.apply_symm_apply] using h
  intro x y h
  apply (MvPolynomial.C_injective (σ := σ × ℕ))
  apply hc'
  simpa only [smul_eq_mul, map_mul] using
    congrArg (MvPolynomial.C : B →+* MvPolynomial (σ × ℕ) B) h

/-- 前段商のφ^(N+1)(d)係数像が正則なら、次の実δ関係はその商上で非零因子。 -/
theorem deltaDivisionFiniteStage_next_isSMulRegular_of_frobenius_regular (N : ℕ) (s : σ)
    (hc : IsSMulRegular (L₀ ⧸ I₀ N)
      (Ideal.Quotient.mk (I₀ N) (MvPolynomial.C (D.frobeniusLift^[N + 1] d)))) :
    IsSMulRegular (L₀ ⧸ I₀ N)
      (Ideal.Quotient.mk (I₀ N) (deltaDivisionIteratedRelation D d a s (N + 1))) := by
  let J := deltaDivisionFiniteStageInitialIdeal D d a N
  let e := deltaDivisionFiniteStageTailQuotientEquiv D d a N
  have hc' := deltaDivisionFiniteStageInitialQuotient_coefficient_isSMulRegular D d a N
    (D.frobeniusLift^[N + 1] d) hc
  have hr := linear_mvpolynomial_regular (Ideal.Quotient.mk J
    (MvPolynomial.C (D.frobeniusLift^[N + 1] d)))
    (Ideal.Quotient.mk J (deltaDivisionFiniteLeadingLowerPolynomial D d a s (N + 1)))
    (s, 0) hc'
  have he := deltaDivisionFiniteStageTailQuotientEquiv_next D d a N s
  change e (Ideal.Quotient.mk (I₀ N) (deltaDivisionIteratedRelation D d a s (N + 1))) = _ at he
  intro x y h
  apply e.injective
  apply hr
  have hh := congrArg e h
  simpa only [smul_eq_mul, map_mul, he] using hh

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteRelationsRegular

/-! ## Frobenius入力の係数イデアルと次のp除算入力の正則性 -/

@[expose] public noncomputable section DeltaPDivisionNextInput

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- φ(y_s)とy_s^pはpの倍数だけ異なり、raw残余の適切な係数イデアルは同じ。 -/
theorem deltaPDivisionFirstBaseIdeal_frobenius_eq_power (D : DeltaStructure p A) (y : σ → A) :
    deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ D.frobeniusLift (y s)) =
      deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p) := by
  let I := deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ D.frobeniusLift (y s))
  let J := deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p)
  have hpI : (p : A) ∈ I := by
    apply (show Ideal.span {(p : A), (p : A)} ≤ I from le_sup_left)
    exact Ideal.subset_span (by simp)
  have hpJ : (p : A) ∈ J := by
    apply (show Ideal.span {(p : A), (p : A)} ≤ J from le_sup_left)
    exact Ideal.subset_span (by simp)
  apply le_antisymm
  · refine sup_le le_sup_left (Ideal.span_le.mpr ?_)
    rintro t ⟨s, rfl⟩
    change D.frobeniusLift (y s) ∈ J
    rw [D.frobeniusLift_apply]
    have hs : y s ^ p ∈ J := by
      apply (show Ideal.span (Set.range (fun s ↦ y s ^ p)) ≤ J from le_sup_right)
      exact Ideal.subset_span (Set.mem_range_self s)
    exact J.add_mem hs (J.mul_mem_right (D.delta (y s)) hpJ)
  · refine sup_le le_sup_left (Ideal.span_le.mpr ?_)
    rintro t ⟨s, rfl⟩
    change y s ^ p ∈ I
    have hs : D.frobeniusLift (y s) ∈ I := by
      apply (show Ideal.span (Set.range (fun s ↦ D.frobeniusLift (y s))) ≤ I from le_sup_right)
      exact Ideal.subset_span (Set.mem_range_self s)
    have he : y s ^ p = D.frobeniusLift (y s) - (p : A) * D.delta (y s) := by
      rw [D.frobeniusLift_apply, add_sub_cancel_right]
    rw [he]
    exact I.sub_mem hs (I.mul_mem_right (D.delta (y s)) hpI)

omit [Fact p.Prime] in
/-- 定数一元族のp乗入力に対する係数イデアルは、具体的な(p,y^p)。 -/
theorem deltaPDivisionFirstBaseIdeal_const_power [Nonempty σ] (y : A) :
    deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun _ : σ ↦ y ^ p) =
      Ideal.span {(p : A), y ^ p} := by
  rw [deltaDivisionFirstBaseIdeal, Set.range_const]
  have hp : Ideal.span {(p : A), (p : A)} = Ideal.span {(p : A)} :=
    congrArg Ideal.span (Set.insert_eq_of_mem (Set.mem_singleton (p : A)))
  rw [hp, ← Ideal.span_insert]

/-- A/(p,y_s^p)で正則な元の像は、任意元族raw A{φ(y_s)/p}の実p商でも正則。 -/
theorem deltaPDivisionRawModP_next_isSMulRegular
    (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (y : σ → A) (w : Aˣ) (hw : (w : A) = D.delta (p : A)) (x : A)
    (hx : IsSMulRegular
      (A ⧸ deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p))
      (Ideal.Quotient.mk (deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ y s ^ p)) x)) :
    IsSMulRegular
      (DeltaAdjoinDivision D (p : A) (fun s ↦ D.frobeniusLift (y s)) ⧸
        Ideal.span {(p : DeltaAdjoinDivision D (p : A) (fun s ↦ D.frobeniusLift (y s)))})
      (Ideal.Quotient.mk
        (Ideal.span {(p : DeltaAdjoinDivision D (p : A) (fun s ↦ D.frobeniusLift (y s)))})
        (deltaAdjoinDivisionMap D (p : A) (fun s ↦ D.frobeniusLift (y s)) x)) := by
  let e := Ideal.quotEquivOfEq (deltaPDivisionFirstBaseIdeal_frobenius_eq_power D y)
  have hr : IsSMulRegular
      (A ⧸ deltaDivisionFirstBaseIdeal (p := p) (p : A) (fun s ↦ D.frobeniusLift (y s)))
      (Ideal.Quotient.mk (deltaDivisionFirstBaseIdeal (p := p) (p : A)
        (fun s ↦ D.frobeniusLift (y s))) x) := by
    intro z t hzt
    change Ideal.Quotient.mk _ x * z = Ideal.Quotient.mk _ x * t at hzt
    apply e.injective
    apply hx
    change Ideal.Quotient.mk _ x * e z = Ideal.Quotient.mk _ x * e t
    have h := congrArg e hzt
    rw [map_mul, map_mul, Ideal.quotEquivOfEq_mk] at h
    exact h
  exact deltaAdjoinDivisionModP_next_isSMulRegular D hpA hg
    (fun s ↦ D.frobeniusLift (y s)) w hw x hr

end SerrePositivity.BhattScholze

end DeltaPDivisionNextInput
