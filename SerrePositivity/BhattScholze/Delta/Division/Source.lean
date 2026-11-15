module

public import SerrePositivity.BhattScholze.Delta.Division.Relations
public import Mathlib.RingTheory.TensorProduct.Maps
public import SerrePositivity.BhattScholze.Delta.Division.Family
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Logic.Equiv.Set
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.HomologicalAlgebra.TorFlatBaseChangeVanishing
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeRightTensor
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedAssociator
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing

/-!
# 自由 δ 射の評価源と係数商還元

## 概要
一般の除数・任意元族の自由 δ 射が与える代数構造、評価源と raw δ 包の核表示、有限 δ 関係と有限評価関係、任意有限根族の次段関係から評価関係への移送、分母 1 の raw 包、部分根族と補集合の自由 δ 変数の分離、有限部分族から任意族への p 正則性の移送、係数商への降下・基底変更・右因子への移送と Tor の消滅、自由 δ 射の通常テンソル積とその δ 構造。
BS 著者版 Corollary 2.39 と Proposition 3.13 の包に使う、自由 δ 射の評価源と係数商を比較する。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Andre/Envelope/DivisionResidue`、`Andre/Envelope/FamilyEvaluation`、`Andre/Envelope/MonicCandidate`、`Andre/Envelope/MonicSource`、`Andre/Envelope/PDivisionSource`、`Andre/Envelope/RootFamilyRaw`、`Andre/Envelope/RootFamilySource`、`Andre/Envelope/RootSource`、`Andre/Envelope/SourceEvaluation`、`Andre/PowerRootEnvelope/Unconditional/Localization`、`Andre/PowerRootEnvelope/Unconditional/Source`、`Andre/Variants/RootedExtension`、`Semiperfectoid/Surjectivity/RootEnvelope/Source`。
-/

universe u v w

/-! ## 実有限δ関係と自由δ射の有限評価関係

δ^n(u−v)とδ^n(u)−δ^n(v)は一般には等しくないが、全深さ≤Nで生成するイデアルは一致する。
この通常イデアル比較だけで導来基底変更の同定を主張しない。
-/

@[expose] public noncomputable section DeltaDivisionFiniteEvaluationRelations

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

private theorem delta_span_to (D : DeltaStructure p A) (s : Set A) (J : Ideal A)
    (hle : Ideal.span s ≤ J) (hgen : ∀ x ∈ s, D.delta x ∈ J)
    {x : A} (hx : x ∈ Ideal.span s) : D.delta x ∈ J := by
  change x ∈ Submodule.span A s at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [D.delta_add]
      exact J.add_mem (J.add_mem ihx ihy) (DeltaStructure.additionCarry_mem J (hle hx) (hle hy))
  | smul r x hx ih =>
      change D.delta (r * x) ∈ J
      rw [D.delta_mul]
      exact J.add_mem (J.add_mem (J.mul_mem_left _ ih)
        (J.mul_mem_left _ (J.pow_mem_of_mem (hle hx) p (Fact.out : p.Prime).pos)))
        (J.mul_mem_left _ ih)

private theorem delta_sub_correction_mem (D : DeltaStructure p A) (J : Ideal A) (x y : A)
    (hxy : x - y ∈ J) : D.delta x - D.delta y - D.delta (x - y) ∈ J := by
  let q := Ideal.Quotient.mk J
  have hz : q (x - y) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hxy
  have hc : q ((WittVector.teichmuller p (x - y) + WittVector.teichmuller p y).coeff 1) = 0 := by
    rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
      WittVector.map_teichmuller, hz, WittVector.teichmuller_zero, zero_add]
    simp
  have h := congrArg q (D.delta_add (x - y) y)
  rw [sub_add_cancel, map_add, map_add, hc, add_zero] at h
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (D.delta x - D.delta y - D.delta (x - y)) = 0
  rw [map_sub, map_sub, h]
  ring

private def pairEvaluationIdeal (D : DeltaStructure p A) (x y : σ → A) (N : ℕ) : Ideal A :=
  Ideal.span (Set.range fun z : σ × Fin (N + 1) =>
    D.delta^[z.2.val] (x z.1) - D.delta^[z.2.val] (y z.1))

private def pairDifferenceIdeal (D : DeltaStructure p A) (x y : σ → A) (N : ℕ) : Ideal A :=
  Ideal.span (Set.range fun z : σ × Fin (N + 1) => D.delta^[z.2.val] (x z.1 - y z.1))

private theorem pairEvaluationIdeal_mono (D : DeltaStructure p A) (x y : σ → A) :
    Monotone (pairEvaluationIdeal D x y) := by
  intro N M h
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨s, i⟩, rfl⟩
  exact Ideal.subset_span ⟨(s, ⟨i.val, by omega⟩), rfl⟩

private theorem pairDifferenceIdeal_mono (D : DeltaStructure p A) (x y : σ → A) :
    Monotone (pairDifferenceIdeal D x y) := by
  intro N M h
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨s, i⟩, rfl⟩
  exact Ideal.subset_span ⟨(s, ⟨i.val, by omega⟩), rfl⟩

private theorem pairDifferenceIdeal_delta (D : DeltaStructure p A) (x y : σ → A) (N : ℕ)
    {z : A} (hz : z ∈ pairDifferenceIdeal D x y N) :
    D.delta z ∈ pairDifferenceIdeal D x y (N + 1) := by
  apply delta_span_to D _ _ (pairDifferenceIdeal_mono D x y (Nat.le_succ N)) ?_ hz
  rintro _ ⟨⟨s, i⟩, rfl⟩
  apply Ideal.subset_span
  exact ⟨(s, ⟨i.val + 1, by omega⟩), Function.iterate_succ_apply' D.delta _ _⟩

private theorem pairEvaluationIdeal_delta (D : DeltaStructure p A) (x y : σ → A) (N : ℕ)
    {z : A} (hz : z ∈ pairEvaluationIdeal D x y N) :
    D.delta z ∈ pairEvaluationIdeal D x y (N + 1) := by
  apply delta_span_to D _ _ (pairEvaluationIdeal_mono D x y (Nat.le_succ N)) ?_ hz
  rintro _ ⟨⟨s, i⟩, rfl⟩
  have hmem : D.delta^[i.val] (x s) - D.delta^[i.val] (y s) ∈
      pairEvaluationIdeal D x y (N + 1) :=
    Ideal.subset_span ⟨(s, ⟨i.val, by omega⟩), rfl⟩
  have hnext : D.delta (D.delta^[i.val] (x s)) - D.delta (D.delta^[i.val] (y s)) ∈
      pairEvaluationIdeal D x y (N + 1) := by
    have hm : D.delta^[i.val + 1] (x s) - D.delta^[i.val + 1] (y s) ∈
        pairEvaluationIdeal D x y (N + 1) :=
      Ideal.subset_span ⟨(s, ⟨i.val + 1, by omega⟩), rfl⟩
    simpa only [Function.iterate_succ_apply'] using hm
  have hc := delta_sub_correction_mem D _ _ _ hmem
  convert (pairEvaluationIdeal D x y (N + 1)).sub_mem hnext hc using 1; abel

private theorem pairEvaluation_mem_difference (D : DeltaStructure p A) (x y : σ → A)
    (s : σ) (N : ℕ) :
    D.delta^[N] (x s) - D.delta^[N] (y s) ∈ pairDifferenceIdeal D x y N := by
  induction N with
  | zero => exact Ideal.subset_span ⟨(s, 0), rfl⟩
  | succ N ih =>
      have hd := pairDifferenceIdeal_delta D x y N ih
      have hi := pairDifferenceIdeal_mono D x y (Nat.le_succ N) ih
      have hc := delta_sub_correction_mem D _ _ _ hi
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      convert (pairDifferenceIdeal D x y (N + 1)).add_mem hc hd using 1; abel

private theorem pairDifference_mem_evaluation (D : DeltaStructure p A) (x y : σ → A)
    (s : σ) (N : ℕ) :
    D.delta^[N] (x s - y s) ∈ pairEvaluationIdeal D x y N := by
  induction N with
  | zero => exact Ideal.subset_span ⟨(s, 0), rfl⟩
  | succ N ih =>
      rw [Function.iterate_succ_apply']
      exact pairEvaluationIdeal_delta D x y N ih

private theorem pairIdeals_eq (D : DeltaStructure p A) (x y : σ → A) (N : ℕ) :
    pairEvaluationIdeal D x y N = pairDifferenceIdeal D x y N := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    exact pairDifferenceIdeal_mono D x y (by omega : i.val ≤ N)
      (pairEvaluation_mem_difference D x y s i.val)
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    exact pairEvaluationIdeal_mono D x y (by omega : i.val ≤ N)
      (pairDifference_mem_evaluation D x y s i.val)

/-- 自由δ射の座標評価から生じる深さnの実除算関係。 -/
def deltaDivisionEvaluationRelation (D : DeltaStructure p A) (d : A) (a : σ → A)
    (s : σ) (n : ℕ) : RelativeFreeDeltaRing (R := A) σ :=
  (relativeFreeDeltaStructure σ D).delta^[n] (MvPolynomial.C d * MvPolynomial.X (s, 0)) -
    (relativeFreeDeltaStructure σ D).delta^[n] (MvPolynomial.C (a s))

/-- 評価関係の定数側は、基底δ環の実反復δ座標の係数像。 -/
theorem deltaDivisionEvaluationRelation_eq (D : DeltaStructure p A) (d : A) (a : σ → A)
    (s : σ) (n : ℕ) :
    deltaDivisionEvaluationRelation D d a s n =
      (relativeFreeDeltaStructure σ D).delta^[n] (MvPolynomial.C d * MvPolynomial.X (s, 0)) -
        MvPolynomial.C (D.delta^[n] (a s)) := by
  have hc : ∀ k : ℕ, (relativeFreeDeltaStructure σ D).delta^[k] (MvPolynomial.C (a s)) =
      MvPolynomial.C (D.delta^[k] (a s)) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        relativeFreeDeltaStructure_delta_C]
  exact congrArg (fun z =>
    (relativeFreeDeltaStructure σ D).delta^[n]
      (MvPolynomial.C d * MvPolynomial.X (s, 0)) - z) (hc n)

/-- 自由δ射の全深さ≤Nの評価関係で生成した実通常イデアル。 -/
def deltaDivisionFiniteEvaluationIdeal (D : DeltaStructure p A) (d : A) (a : σ → A)
    (N : ℕ) : Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  Ideal.span (Set.range fun z : σ × Fin (N + 1) =>
    deltaDivisionEvaluationRelation D d a z.1 z.2.val)

/-- 全有限段で、自由δ射の評価関係と既存の実反復差関係が同じイデアルを生成する。 -/
theorem deltaDivisionFiniteEvaluationIdeal_eq (D : DeltaStructure p A) (d : A) (a : σ → A)
    (N : ℕ) :
    deltaDivisionFiniteEvaluationIdeal D d a N = deltaDivisionFiniteRelationIdeal D d a N := by
  exact pairIdeals_eq (relativeFreeDeltaStructure σ D)
    (fun s => MvPolynomial.C d * MvPolynomial.X (s, 0)) (fun s => MvPolynomial.C (a s)) N

/-- 各評価関係は既存の実有限段イデアルに属する。 -/
theorem deltaDivisionEvaluationRelation_mem_finite (D : DeltaStructure p A) (d : A) (a : σ → A)
    (s : σ) (n N : ℕ) (hn : n ≤ N) :
    deltaDivisionEvaluationRelation D d a s n ∈ deltaDivisionFiniteRelationIdeal D d a N := by
  rw [← deltaDivisionFiniteEvaluationIdeal_eq]
  exact Ideal.subset_span ⟨(s, ⟨n, by omega⟩), rfl⟩

/-- 全下位関係の後では、一根の次の評価関係とδ反復関係は同じイデアルを追加する。 -/
theorem deltaDivisionEvaluation_next_sup_span_eq (D : DeltaStructure p A) (d : A)
    (a : σ → A) (t : σ) (N : ℕ) :
    deltaDivisionFiniteRelationIdeal D d a N ⊔
        Ideal.span {deltaDivisionEvaluationRelation D d a t (N + 1)} =
      deltaDivisionFiniteRelationIdeal D d a N ⊔
        Ideal.span {deltaDivisionIteratedRelation D d a t (N + 1)} := by
  let E := relativeFreeDeltaStructure σ D
  let x : Unit → RelativeFreeDeltaRing (R := A) σ :=
    fun _ => MvPolynomial.C d * MvPolynomial.X (t, 0)
  let y : Unit → RelativeFreeDeltaRing (R := A) σ := fun _ => MvPolynomial.C (a t)
  have hEval : deltaDivisionEvaluationRelation D d a t (N + 1) ∈
      deltaDivisionFiniteRelationIdeal D d a N ⊔
        Ideal.span {deltaDivisionIteratedRelation D d a t (N + 1)} := by
    have hm := pairEvaluation_mem_difference E x y () (N + 1)
    apply (show pairDifferenceIdeal E x y (N + 1) ≤ _ from Ideal.span_le.mpr ?_) hm
    rintro _ ⟨⟨_, i⟩, rfl⟩
    by_cases hi : i.val ≤ N
    · apply (show deltaDivisionFiniteRelationIdeal D d a N ≤ _ from le_sup_left)
      exact Ideal.subset_span ⟨(t, ⟨i.val, by omega⟩), rfl⟩
    · have he : i.val = N + 1 := by omega
      change deltaDivisionIteratedRelation D d a t i.val ∈ _
      rw [he]
      exact (show Ideal.span {deltaDivisionIteratedRelation D d a t (N + 1)} ≤ _
        from le_sup_right) (Ideal.mem_span_singleton_self _)
  have hIter : deltaDivisionIteratedRelation D d a t (N + 1) ∈
      deltaDivisionFiniteRelationIdeal D d a N ⊔
        Ideal.span {deltaDivisionEvaluationRelation D d a t (N + 1)} := by
    have hm := pairDifference_mem_evaluation E x y () (N + 1)
    apply (show pairEvaluationIdeal E x y (N + 1) ≤ _ from Ideal.span_le.mpr ?_) hm
    rintro _ ⟨⟨_, i⟩, rfl⟩
    by_cases hi : i.val ≤ N
    · exact (show deltaDivisionFiniteRelationIdeal D d a N ≤ _ from le_sup_left)
        (deltaDivisionEvaluationRelation_mem_finite D d a t i.val N hi)
    · have he : i.val = N + 1 := by omega
      change deltaDivisionEvaluationRelation D d a t i.val ∈ _
      rw [he]
      exact (show Ideal.span {deltaDivisionEvaluationRelation D d a t (N + 1)} ≤ _
        from le_sup_right) (Ideal.mem_span_singleton_self _)
  apply le_antisymm
  · exact sup_le le_sup_left (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hEval))
  · exact sup_le le_sup_left (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hIter))

/-- 自由δ射の全評価関係は、実raw δ除算包の標準商射で零となる。 -/
theorem deltaDivisionEvaluationRelation_quotient_eq_zero
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
      (deltaDivisionRelationIdeal d a)) (deltaDivisionEvaluationRelation D d a s n) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [deltaDivision_deltaClosure_eq_iSup_finiteRelations]
  exact (le_iSup (deltaDivisionFiniteRelationIdeal D d a) n)
    (deltaDivisionEvaluationRelation_mem_finite D d a s n n le_rfl)

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteEvaluationRelations

/-! ## 自由δ射の評価源とraw δ包の核表示

源P=A{x_s}からx_s↦d z_sとx_s↦a_sの二つの実δ射を置く。
座標グラフ核の像が、既存raw δ除算包の実定義イデアルとなることを証明する。
-/

@[expose] public noncomputable section DeltaDivisionEvaluationSource

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 源自由δ環から、初期変数x_sをd z_sへ送る実δ射の underlying 環射。 -/
def deltaDivisionSourceMap (D : DeltaStructure p A) (d : A) :
    RelativeFreeDeltaRing (R := A) σ →+* RelativeFreeDeltaRing (R := A) σ :=
  relativeFreeDeltaEval (relativeFreeDeltaStructure σ D) MvPolynomial.C
    (fun s => MvPolynomial.C d * MvPolynomial.X (s, 0))

/-- 源自由δ環からa_sへ評価する実環射。 -/
def deltaDivisionSourceEval (D : DeltaStructure p A) (a : σ → A) :
    RelativeFreeDeltaRing (R := A) σ →+* A :=
  relativeFreeDeltaEval D (RingHom.id A) a

/-- d z_sへの自由評価射は既存δ構造を保存する。 -/
theorem deltaDivisionSourceMap_isDeltaHom (D : DeltaStructure p A) (d : A) :
    (relativeFreeDeltaStructure σ D).IsDeltaHom (relativeFreeDeltaStructure σ D)
      (deltaDivisionSourceMap D d) :=
  relativeFreeDeltaEval_isDeltaHom D _ _ (relativeFreeDeltaStructure_C_isDeltaHom σ D) _

/-- a_sへの自由評価射も既存δ構造を保存する。 -/
theorem deltaDivisionSourceEval_isDeltaHom (D : DeltaStructure p A) (a : σ → A) :
    (relativeFreeDeltaStructure σ D).IsDeltaHom D (deltaDivisionSourceEval D a) :=
  relativeFreeDeltaEval_isDeltaHom D D _ (fun _ => rfl) a

/-- 源自由δ射は元の係数を固定する。 -/
theorem deltaDivisionSourceMap_C (D : DeltaStructure p A) (d r : A) :
    deltaDivisionSourceMap (σ := σ) D d (MvPolynomial.C r) = MvPolynomial.C r :=
  relativeFreeDeltaEval_C _ _ _ _

/-- 源評価射も元の係数上では恒等写像。 -/
theorem deltaDivisionSourceEval_C (D : DeltaStructure p A) (a : σ → A) (r : A) :
    deltaDivisionSourceEval D a (MvPolynomial.C r) = r :=
  relativeFreeDeltaEval_C _ _ _ _

/-- 全δ座標の像はd z_sの実反復δ像。 -/
theorem deltaDivisionSourceMap_X (D : DeltaStructure p A) (d : A) (s : σ) (n : ℕ) :
    deltaDivisionSourceMap D d (MvPolynomial.X (s, n)) =
      (relativeFreeDeltaStructure σ D).delta^[n] (MvPolynomial.C d * MvPolynomial.X (s, 0)) :=
  relativeFreeDeltaEval_X _ _ _ _ _

/-- 全δ座標の評価はa_sの実反復δ像。 -/
theorem deltaDivisionSourceEval_X (D : DeltaStructure p A) (a : σ → A) (s : σ) (n : ℕ) :
    deltaDivisionSourceEval D a (MvPolynomial.X (s, n)) = D.delta^[n] (a s) :=
  relativeFreeDeltaEval_X _ _ _ _ _

/-- 源評価射の核は、全座標グラフ関係で生成される。 -/
theorem deltaDivisionSourceEval_ker (D : DeltaStructure p A) (a : σ → A) :
    RingHom.ker (deltaDivisionSourceEval D a) =
      Ideal.span (Set.range fun z : σ × ℕ =>
        MvPolynomial.X z - MvPolynomial.C (D.delta^[z.2] (a z.1))) := by
  let K : Ideal (RelativeFreeDeltaRing (R := A) σ) :=
    Ideal.span (Set.range fun z : σ × ℕ =>
      MvPolynomial.X z - MvPolynomial.C (D.delta^[z.2] (a z.1)))
  have hK : K ≤ RingHom.ker (deltaDivisionSourceEval D a) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, n⟩, rfl⟩
    change deltaDivisionSourceEval D a
      (MvPolynomial.X (s, n) - MvPolynomial.C (D.delta^[n] (a s))) = 0
    rw [map_sub, deltaDivisionSourceEval_X, deltaDivisionSourceEval_C, sub_self]
  let q := Ideal.Quotient.mk K
  have hq : q = (q.comp MvPolynomial.C).comp (deltaDivisionSourceEval D a) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, RingHom.comp_apply, deltaDivisionSourceEval_C]
    · rintro ⟨s, n⟩
      rw [RingHom.comp_apply, RingHom.comp_apply, deltaDivisionSourceEval_X]
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(s, n), rfl⟩)
  apply le_antisymm ?_ hK
  intro f hf
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q f = 0
  rw [hq]
  change q (MvPolynomial.C (deltaDivisionSourceEval D a f)) = 0
  rw [show deltaDivisionSourceEval D a f = 0 from hf, map_zero, map_zero]

/-- 核の座標グラフ関係の像は、前工程の実評価関係そのもの。 -/
theorem deltaDivisionSourceMap_graphRelation (D : DeltaStructure p A) (d : A) (a : σ → A)
    (s : σ) (n : ℕ) :
    deltaDivisionSourceMap D d
      (MvPolynomial.X (s, n) - MvPolynomial.C (D.delta^[n] (a s))) =
      deltaDivisionEvaluationRelation D d a s n := by
  rw [map_sub, deltaDivisionSourceMap_X, deltaDivisionSourceMap_C,
    deltaDivisionEvaluationRelation_eq]

/-- 源評価射の核の像イデアルは、実raw δ除算包の定義δ閉包。 -/
theorem deltaDivisionSourceMap_eval_ker (D : DeltaStructure p A) (d : A) (a : σ → A) :
    (RingHom.ker (deltaDivisionSourceEval D a)).map (deltaDivisionSourceMap D d) =
      (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a) := by
  rw [deltaDivisionSourceEval_ker, Ideal.map_span, ← Set.range_comp']
  change Ideal.span (Set.range fun z : σ × ℕ => deltaDivisionSourceMap D d
    (MvPolynomial.X z - MvPolynomial.C (D.delta^[z.2] (a z.1)))) = _
  have hg : (fun z : σ × ℕ => deltaDivisionSourceMap D d
      (MvPolynomial.X z - MvPolynomial.C (D.delta^[z.2] (a z.1)))) =
      (fun z : σ × ℕ => deltaDivisionEvaluationRelation D d a z.1 z.2) :=
    funext (fun z => deltaDivisionSourceMap_graphRelation D d a z.1 z.2)
  rw [hg]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, n⟩, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      (deltaDivisionEvaluationRelation_quotient_eq_zero D d a s n)
  · rw [deltaDivision_deltaClosure_eq_iSup_finiteRelations]
    apply iSup_le
    intro N
    rw [← deltaDivisionFiniteEvaluationIdeal_eq]
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, i⟩, rfl⟩
    exact Ideal.subset_span ⟨(s, i.val), rfl⟩

/-- 実raw商射と基底射は、源自由δ射と源評価射の四角を可換にする。 -/
theorem deltaDivisionSource_raw_square (D : DeltaStructure p A) (d : A) (a : σ → A) :
    (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
      (deltaDivisionRelationIdeal d a))).comp (deltaDivisionSourceMap D d) =
        (deltaAdjoinDivisionMap D d a).comp (deltaDivisionSourceEval D a) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, deltaDivisionSourceMap_C, deltaDivisionSourceEval_C]
    rfl
  · rintro ⟨s, n⟩
    simp only [RingHom.comp_apply, deltaDivisionSourceMap_X, deltaDivisionSourceEval_X]
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk _
      ((relativeFreeDeltaStructure σ D).delta^[n] (MvPolynomial.C d * MvPolynomial.X (s, 0))) -
        Ideal.Quotient.mk _ (MvPolynomial.C (D.delta^[n] (a s))) = 0
    rw [← map_sub, ← deltaDivisionEvaluationRelation_eq]
    exact deltaDivisionEvaluationRelation_quotient_eq_zero D d a s n

/-- raw δ包は、具体的な自由δ射と評価射の通常の可換環pushoutを与える。
終域のδ構造や完備性を仮定しない。導来pushoutの主張とは区別する。 -/
theorem existsUnique_deltaDivisionSourceRawLift {B : Type*} [CommRing B]
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (f : A →+* B) (g : RelativeFreeDeltaRing (R := A) σ →+* B)
    (h : g.comp (deltaDivisionSourceMap D d) = f.comp (deltaDivisionSourceEval D a)) :
    ∃! k : DeltaAdjoinDivision D d a →+* B,
      k.comp (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal d a))) = g ∧
      k.comp (deltaAdjoinDivisionMap D d a) = f := by
  let J := (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a)
  have hJ : J ≤ RingHom.ker g := by
    change (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a) ≤ _
    rw [← deltaDivisionSourceMap_eval_ker]
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change g (deltaDivisionSourceMap D d r) = 0
    have he := RingHom.congr_fun h r
    change g (deltaDivisionSourceMap D d r) = f (deltaDivisionSourceEval D a r) at he
    rw [he, show deltaDivisionSourceEval D a r = 0 from hr, map_zero]
  let k := Ideal.Quotient.lift J g hJ
  have hk : k.comp (Ideal.Quotient.mk J) = g := by
    apply RingHom.ext
    intro r
    exact Ideal.Quotient.lift_mk J g hJ
  refine ⟨k, ⟨hk, ?_⟩, ?_⟩
  · apply RingHom.ext
    intro r
    change k (Ideal.Quotient.mk J (MvPolynomial.C r)) = f r
    rw [Ideal.Quotient.lift_mk]
    have he := RingHom.congr_fun h (MvPolynomial.C r)
    simpa only [RingHom.comp_apply, deltaDivisionSourceMap_C, deltaDivisionSourceEval_C] using he
  · intro l hl
    apply Ideal.Quotient.ringHom_ext
    exact hl.1.trans hk.symm

end SerrePositivity.BhattScholze

end DeltaDivisionEvaluationSource

/-! ## 一般除数・任意元族の自由δ射が与える実代数構造 -/

@[expose] public noncomputable section DeltaDivisionSourceAlgebras

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 任意元族cへの実自由δ評価βによる係数環の源代数構造。 -/
@[instance_reducible]
def deltaDivisionSourceEvaluationAlgebra (D : DeltaStructure p A) (c : σ → A) :
    Algebra (RelativeFreeDeltaRing (R := A) σ) A :=
  (deltaDivisionSourceEval D c).toAlgebra

/-- 実自由δ射α:x_s↦d z_sによる終域の源代数構造。 -/
@[instance_reducible]
def deltaDivisionSourceTargetAlgebra (D : DeltaStructure p A) (d : A) :
    Algebra (RelativeFreeDeltaRing (R := A) σ) (RelativeFreeDeltaRing (R := A) σ) :=
  (deltaDivisionSourceMap (σ := σ) D d).toAlgebra

/-- 評価代数構造の実係数射は指定したβそのもの。 -/
theorem deltaDivisionSourceEvaluationAlgebra_algebraMap (D : DeltaStructure p A) (c : σ → A) :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    algebraMap (RelativeFreeDeltaRing (R := A) σ) A = deltaDivisionSourceEval D c := rfl

/-- 終域代数構造の実係数射は指定したαそのもの。 -/
theorem deltaDivisionSourceTargetAlgebra_algebraMap (D : DeltaStructure p A) (d : A) :
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    algebraMap (RelativeFreeDeltaRing (R := A) σ) (RelativeFreeDeltaRing (R := A) σ) =
      deltaDivisionSourceMap (σ := σ) D d := rfl

end SerrePositivity.BhattScholze

end DeltaDivisionSourceAlgebras

/-! ## 実自由δ射の通常テンソル積とraw δ包

源Pと終域Lは同じ underlying 型だが、LのP代数構造はα:x↦d zによるもの。
通常テンソル積の標準写像を保つ比較を構成し、導来テンソルの離散性とは区別する。
-/

@[expose] public noncomputable section DeltaDivisionSourceTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} {σ : Type v} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (c : σ → A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => c
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D d
local notation "β₀" => deltaDivisionSourceEval D a₀
local notation "B₀" => DeltaAdjoinDivision D d a₀
local notation "j₀" => deltaAdjoinDivisionMap D d a₀
local notation "q₀" => Ideal.Quotient.mk
  (DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
    (deltaDivisionRelationIdeal d a₀))

/-- raw包の源P代数構造は、基底射jと評価βの合成で与える。 -/
@[instance_reducible] def deltaDivisionSourceRawAlgebra : Algebra P₀ B₀ :=
  ((j₀).comp β₀).toAlgebra

/-- raw包の源作用は、βで作用するAを経由する。 -/
theorem deltaDivisionSourceRawTower :
    let := deltaDivisionSourceEvaluationAlgebra D c
    let := deltaDivisionSourceRawAlgebra (σ := σ) D d c
    let : Module P₀ B₀ := Algebra.toModule
    @IsScalarTower P₀ A B₀
      (deltaDivisionSourceEvaluationAlgebra D c).toSMul
      (inferInstance : Algebra A B₀).toSMul
      (deltaDivisionSourceRawAlgebra (σ := σ) D d c).toSMul := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceRawAlgebra (σ := σ) D d c
  let : Module P₀ B₀ := Algebra.toModule
  exact IsScalarTower.of_algebraMap_eq (R := P₀) (S := A) (A := B₀) (fun _ => rfl)

/-- raw標準商射を源P上の代数射として表す。 -/
def deltaDivisionSourceRawRight :
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    letI := deltaDivisionSourceRawAlgebra (σ := σ) D d c
    letI : Module P₀ B₀ := Algebra.toModule
    P₀ →ₐ[P₀] B₀ := by
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  letI := deltaDivisionSourceRawAlgebra (σ := σ) D d c
  letI : Module P₀ B₀ := Algebra.toModule
  exact
    { __ := q₀
      commutes' := fun r => RingHom.congr_fun (deltaDivisionSource_raw_square D d a₀) r }

/-- 通常テンソル積からraw包への実標準環射。 -/
def deltaDivisionSourceTensorToRaw :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ →+* B₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  letI := deltaDivisionSourceRawAlgebra (σ := σ) D d c
  letI : Module P₀ B₀ := Algebra.toModule
  letI := deltaDivisionSourceRawTower (σ := σ) D d c
  exact (Algebra.TensorProduct.lift (R := P₀) (Algebra.ofId A B₀)
    (deltaDivisionSourceRawRight D d c) (fun _ _ => Commute.all _ _)).toRingHom

/-- テンソルの純元の像は、既存基底射と既存商射の積。 -/
theorem deltaDivisionSourceTensorToRaw_tmul (a : A) (b : P₀) :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    deltaDivisionSourceTensorToRaw D d c (a ⊗ₜ[P₀] b) = j₀ a * q₀ b := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra (σ := σ) D d c
  let : Module P₀ B₀ := Algebra.toModule
  let := deltaDivisionSourceRawTower (σ := σ) D d c
  exact Algebra.TensorProduct.lift_tmul (Algebra.ofId A B₀)
    (deltaDivisionSourceRawRight D d c) (fun _ _ => Commute.all _ _) a b

/-- 通常テンソルの両因子の包含を保つ、raw包からの環射は一意に存在する。 -/
theorem existsUnique_deltaDivisionRawTensorMap :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    ∃! k : B₀ →+* A ⊗[P₀] P₀,
      k.comp q₀ = Algebra.TensorProduct.includeRight.toRingHom ∧
      k.comp j₀ = Algebra.TensorProduct.includeLeftRingHom := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  apply existsUnique_deltaDivisionSourceRawLift D d a₀
  exact (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := P₀) (A := A)
    (B := P₀)).symm

/-- raw包から通常テンソルへの実標準環射。 -/
def deltaDivisionSourceRawToTensor :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    B₀ →+* A ⊗[P₀] P₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  exact Classical.choose (existsUnique_deltaDivisionRawTensorMap (σ := σ) D d c)

/-- rawからテンソルへの射は、元の終域Lの標準像を右因子へ送る。 -/
theorem deltaDivisionSourceRawToTensor_comp_quotient :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaDivisionSourceRawToTensor D d c).comp q₀ =
      Algebra.TensorProduct.includeRight.toRingHom := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  exact (Classical.choose_spec (existsUnique_deltaDivisionRawTensorMap (σ := σ) D d c)).1.1

/-- rawからテンソルへの射は、元の基底Aの標準像を左因子へ送る。 -/
theorem deltaDivisionSourceRawToTensor_comp_base :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaDivisionSourceRawToTensor D d c).comp j₀ = Algebra.TensorProduct.includeLeftRingHom := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  exact (Classical.choose_spec (existsUnique_deltaDivisionRawTensorMap (σ := σ) D d c)).1.2

/-- 実通常テンソル積A⊗_P Lは、既存のraw δ除算包と標準的に環同型。 -/
def deltaDivisionSourceTensorEquiv :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ ≃+* B₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  apply RingEquiv.ofRingHom (deltaDivisionSourceTensorToRaw D d c)
    (deltaDivisionSourceRawToTensor D d c)
  · apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro r
    have h := RingHom.congr_fun (deltaDivisionSourceRawToTensor_comp_quotient (σ := σ) D d c) r
    change deltaDivisionSourceRawToTensor D d c (q₀ r) = 1 ⊗ₜ[P₀] r at h
    change deltaDivisionSourceTensorToRaw D d c (deltaDivisionSourceRawToTensor D d c (q₀ r)) = q₀ r
    rw [h, deltaDivisionSourceTensorToRaw_tmul, map_one, one_mul]
  · apply Algebra.TensorProduct.ringHom_ext
    · apply RingHom.ext
      intro a
      have h := RingHom.congr_fun (deltaDivisionSourceRawToTensor_comp_base (σ := σ) D d c) a
      change deltaDivisionSourceRawToTensor D d c (j₀ a) = a ⊗ₜ[P₀] 1 at h
      change deltaDivisionSourceRawToTensor D d c
        (deltaDivisionSourceTensorToRaw D d c (a ⊗ₜ[P₀] 1)) =
        a ⊗ₜ[P₀] 1
      rw [deltaDivisionSourceTensorToRaw_tmul, map_one, mul_one, h]
    · apply RingHom.ext
      intro r
      have h := RingHom.congr_fun (deltaDivisionSourceRawToTensor_comp_quotient (σ := σ) D d c) r
      change deltaDivisionSourceRawToTensor D d c (q₀ r) = 1 ⊗ₜ[P₀] r at h
      change deltaDivisionSourceRawToTensor D d c
        (deltaDivisionSourceTensorToRaw D d c (1 ⊗ₜ[P₀] r)) =
        1 ⊗ₜ[P₀] r
      rw [deltaDivisionSourceTensorToRaw_tmul, map_one, one_mul, h]

/-- 通常テンソル比較同型の純元上の具体的な式。 -/
theorem deltaDivisionSourceTensorEquiv_tmul (a : A) (b : P₀) :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    deltaDivisionSourceTensorEquiv D d c (a ⊗ₜ[P₀] b) = j₀ a * q₀ b := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  exact deltaDivisionSourceTensorToRaw_tmul D d c a b

/-- 通常テンソル比較同型の逆は、raw標準商元を右因子の標準像へ送る。 -/
theorem deltaDivisionSourceTensorEquiv_symm_quotient (r : P₀) :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaDivisionSourceTensorEquiv D d c).symm (q₀ r) = 1 ⊗ₜ[P₀] r := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  exact RingHom.congr_fun (deltaDivisionSourceRawToTensor_comp_quotient (σ := σ) D d c) r

/-- 通常pushout比較は、元の係数Aの標準作用を保つ代数同型。 -/
def deltaDivisionSourceTensorAlgEquiv :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    A ⊗[P₀] P₀ ≃ₐ[A] B₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  apply AlgEquiv.ofRingEquiv (f := deltaDivisionSourceTensorEquiv D d c)
  intro x
  change deltaDivisionSourceTensorEquiv D d c (x ⊗ₜ[P₀] 1) = j₀ x
  rw [deltaDivisionSourceTensorEquiv_tmul, map_one, mul_one]

end SerrePositivity.BhattScholze

end DeltaDivisionSourceTensor

/-! ## 分母1の実raw δ包と源評価環

自由δ射x↦1·zは恒等射なので、そのraw包は実源評価環そのものとなる。
標準商射・基底射・変数・δ構造との両立を保つ。
-/

@[expose] public noncomputable section DeltaDivisionUnitDenominator

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 実源δ評価射は、元の係数射を切断として全射。 -/
theorem deltaDivisionSourceEval_surjective (D : DeltaStructure p A) (a : σ → A) :
    Function.Surjective (deltaDivisionSourceEval D a) := by
  intro r
  exact ⟨MvPolynomial.C r, deltaDivisionSourceEval_C D a r⟩

/-- 分母1を指定する自由δ射は実恒等射。 -/
theorem deltaDivisionSourceMap_one (D : DeltaStructure p A) :
    deltaDivisionSourceMap (σ := σ) D (1 : A) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    exact deltaDivisionSourceMap_C D 1 r
  · rintro ⟨s, n⟩
    rw [deltaDivisionSourceMap_X, map_one, one_mul]
    have h := relativeFreeDeltaHom_X_iterates D (relativeFreeDeltaStructure σ D)
      (RingHom.id (RelativeFreeDeltaRing (R := A) σ)) (fun _ => rfl) s n
    exact h.symm

/-- 分母1の実定義δ閉包は、実源評価射の核。 -/
theorem deltaDivisionUnitDenominator_ideal (D : DeltaStructure p A) (a : σ → A) :
    (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal (1 : A) a) =
      RingHom.ker (deltaDivisionSourceEval D a) := by
  have h := deltaDivisionSourceMap_eval_ker D (1 : A) a
  rw [deltaDivisionSourceMap_one, Ideal.map_id] at h
  exact h.symm

/-- 分母1のraw δ包と評価環Aの具体的な環同型。 -/
def deltaDivisionUnitDenominatorEquiv (D : DeltaStructure p A) (a : σ → A) :
    DeltaAdjoinDivision D (1 : A) a ≃+* A :=
  (Ideal.quotEquivOfEq (deltaDivisionUnitDenominator_ideal D a)).trans
    ((deltaDivisionSourceEval D a).quotientKerEquivOfSurjective
      (deltaDivisionSourceEval_surjective D a))

/-- 分母1のraw比較は、標準商元を実源δ評価値へ送る。 -/
theorem deltaDivisionUnitDenominatorEquiv_mk (D : DeltaStructure p A) (a : σ → A)
    (r : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionUnitDenominatorEquiv D a (Ideal.Quotient.mk _ r) =
      deltaDivisionSourceEval D a r := by
  rw [deltaDivisionUnitDenominatorEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- 実raw包への基底標準射は、分母1の比較同型で恒等射になる。 -/
theorem deltaDivisionUnitDenominatorEquiv_comp_base (D : DeltaStructure p A) (a : σ → A) :
    (deltaDivisionUnitDenominatorEquiv D a).toRingHom.comp (deltaAdjoinDivisionMap D (1 : A) a) =
      RingHom.id A := by
  apply RingHom.ext
  intro r
  change deltaDivisionUnitDenominatorEquiv D a (Ideal.Quotient.mk _ (MvPolynomial.C r)) = r
  rw [deltaDivisionUnitDenominatorEquiv_mk, deltaDivisionSourceEval_C]

/-- 添加変数は、実評価環の指定元となる。 -/
theorem deltaDivisionUnitDenominatorEquiv_variable (D : DeltaStructure p A) (a : σ → A) (s : σ) :
    deltaDivisionUnitDenominatorEquiv D a (deltaAdjoinDivisionVariable D (1 : A) a s) = a s := by
  change deltaDivisionUnitDenominatorEquiv D a (Ideal.Quotient.mk _ (MvPolynomial.X (s, 0))) = _
  rw [deltaDivisionUnitDenominatorEquiv_mk, deltaDivisionSourceEval_X]
  rfl

/-- 分母1の比較同型の逆射は、既存の実基底標準射そのもの。 -/
theorem deltaDivisionUnitDenominatorEquiv_symm_apply (D : DeltaStructure p A) (a : σ → A) (r : A) :
    (deltaDivisionUnitDenominatorEquiv D a).symm r = deltaAdjoinDivisionMap D (1 : A) a r := by
  apply (deltaDivisionUnitDenominatorEquiv D a).injective
  rw [RingEquiv.apply_symm_apply]
  exact (RingHom.congr_fun (deltaDivisionUnitDenominatorEquiv_comp_base D a) r).symm

/-- 分母1の実環同型は、既存raw δ構造を保つ。 -/
theorem deltaDivisionUnitDenominatorEquiv_isDeltaHom (D : DeltaStructure p A) (a : σ → A) :
    (deltaAdjoinDivisionStructure D (1 : A) a).IsDeltaHom D
      (deltaDivisionUnitDenominatorEquiv D a).toRingHom := by
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change deltaDivisionUnitDenominatorEquiv D a
      ((deltaAdjoinDivisionStructure D (1 : A) a).delta (Ideal.Quotient.mk _ r)) =
    D.delta (deltaDivisionUnitDenominatorEquiv D a (Ideal.Quotient.mk _ r))
  rw [deltaAdjoinDivisionStructure, DeltaStructure.quotient_delta_mk,
    deltaDivisionUnitDenominatorEquiv_mk, deltaDivisionUnitDenominatorEquiv_mk]
  exact deltaDivisionSourceEval_isDeltaHom D a r

end SerrePositivity.BhattScholze

end DeltaDivisionUnitDenominator

/-! ## 有限部分族から任意族raw包へのp正則性の移送 -/

@[expose] public noncomputable section DeltaAdjoinDivisionFamilyRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)

/-- 全有限部分族のp正則性から、その環余極限のp正則性を得る。遷移の単射性は不要。 -/
theorem deltaAdjoinDivisionFiniteColimit_p_mul_injective
    (hp : ∀ T : Finset σ, Function.Injective
      (fun z : DeltaAdjoinDivisionFiniteStage D d a T ↦
        (p : DeltaAdjoinDivisionFiniteStage D d a T) * z)) :
    Function.Injective (fun z : DeltaAdjoinDivisionFiniteColimit D d a ↦
      (p : DeltaAdjoinDivisionFiniteColimit D d a) * z) := by
  classical
  intro x y hxy
  change (p : DeltaAdjoinDivisionFiniteColimit D d a) * x =
    (p : DeltaAdjoinDivisionFiniteColimit D d a) * y at hxy
  apply sub_eq_zero.mp
  have hz : (p : DeltaAdjoinDivisionFiniteColimit D d a) * (x - y) = 0 := by
    rw [mul_sub, hxy, sub_self]
  obtain ⟨T, z, hT⟩ := Ring.DirectLimit.exists_of (x - y)
  have hzero : deltaAdjoinDivisionFiniteColimitOf D d a T
      ((p : DeltaAdjoinDivisionFiniteStage D d a T) * z) = 0 := by
    rw [map_mul, map_natCast]
    change (p : DeltaAdjoinDivisionFiniteColimit D d a) *
      Ring.DirectLimit.of _ _ T z = 0
    rw [hT, hz]
  have hzero' : Ring.DirectLimit.of
      (fun T : Finset σ ↦ DeltaAdjoinDivisionFiniteStage D d a T)
      (fun _ _ h ↦ deltaAdjoinDivisionFiniteMap D d a h) T
      ((p : DeltaAdjoinDivisionFiniteStage D d a T) * z) = 0 := hzero
  obtain ⟨U, hTU, hU⟩ := Ring.DirectLimit.of.zero_exact hzero'
  have hu : deltaAdjoinDivisionFiniteMap D d a hTU z = 0 := by
    apply hp U
    change (p : DeltaAdjoinDivisionFiniteStage D d a U) *
      deltaAdjoinDivisionFiniteMap D d a hTU z =
        (p : DeltaAdjoinDivisionFiniteStage D d a U) * 0
    rw [mul_zero]
    simpa only [map_mul, map_natCast] using hU
  calc
    x - y = deltaAdjoinDivisionFiniteColimitOf D d a T z := hT.symm
    _ = deltaAdjoinDivisionFiniteColimitOf D d a U
        (deltaAdjoinDivisionFiniteMap D d a hTU z) :=
      (deltaAdjoinDivisionFiniteColimitOf_compatible D d a hTU z).symm
    _ = 0 := by rw [hu, map_zero]

/-- 全有限部分族がp正則なら、任意族の実raw包自身がp正則。 -/
theorem deltaAdjoinDivisionFamily_p_mul_injective
    (hp : ∀ T : Finset σ, Function.Injective
      (fun z : DeltaAdjoinDivisionFiniteStage D d a T ↦
        (p : DeltaAdjoinDivisionFiniteStage D d a T) * z)) :
    Function.Injective (fun z : DeltaAdjoinDivision D d a ↦
      (p : DeltaAdjoinDivision D d a) * z) := by
  let e := deltaAdjoinDivisionFiniteColimitEquiv D d a
  intro x y hxy
  apply e.symm.injective
  apply deltaAdjoinDivisionFiniteColimit_p_mul_injective D d a hp
  simpa only [map_mul, map_natCast] using congrArg e.symm hxy

end SerrePositivity.BhattScholze

end DeltaAdjoinDivisionFamilyRegular

/-! ## 任意有限根族の次段δ関係から実評価関係への移送 -/

@[expose] public noncomputable section DeltaDivisionEvaluationFamilyStep

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
variable {T : Type v} [CommRing T] (q : RelativeFreeDeltaRing (R := A) σ →+* T)
variable (N : ℕ) (hI : deltaDivisionFiniteRelationIdeal D d a N ≤ RingHom.ker q)
include hI

/-- 下位関係を消す通常射の後で、次の実評価・δ反復関係は同じ主イデアルを生成する。 -/
theorem deltaDivisionMappedNextEvaluation_span_eq (t : σ) :
    Ideal.span {q (deltaDivisionEvaluationRelation D d a t (N + 1))} =
      Ideal.span {q (deltaDivisionIteratedRelation D d a t (N + 1))} := by
  have h := congrArg (Ideal.map q) (deltaDivisionEvaluation_next_sup_span_eq D d a t N)
  have hz : (deltaDivisionFiniteRelationIdeal D d a N).map q = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker q).mpr hI
  simpa only [Ideal.map_sup, hz, bot_sup_eq, Ideal.map_span, Set.image_singleton] using h

/-- 下位関係を消す通常射の後、次段δ有限族の弱正則性は実評価有限族へ移る。 -/
theorem deltaDivisionMappedNextEvaluation_fin_isWeaklyRegular {m : ℕ} (s : Fin m → σ)
    (hr : RingTheory.Sequence.IsWeaklyRegular T (List.ofFn fun i =>
      q (deltaDivisionIteratedRelation D d a (s i) (N + 1)))) :
    RingTheory.Sequence.IsWeaklyRegular T (List.ofFn fun i =>
      q (deltaDivisionEvaluationRelation D d a (s i) (N + 1))) := by
  let f : σ → T := fun t => q (deltaDivisionEvaluationRelation D d a t (N + 1))
  let g : σ → T := fun t => q (deltaDivisionIteratedRelation D d a t (N + 1))
  have hspan (t : σ) : Ideal.span {f t} = Ideal.span {g t} :=
    deltaDivisionMappedNextEvaluation_span_eq D d a q N hI t
  have hList (l : List σ) : Ideal.ofList (l.map f) = Ideal.ofList (l.map g) := by
    induction l with
    | nil => rfl
    | cons t l ih => simp only [List.map_cons, Ideal.ofList_cons, hspan, ih]
  constructor
  intro i hi
  have hi' : i < m := by simpa only [List.length_ofFn] using hi
  have hw := hr.regular_mod_prev i (by simpa only [List.length_ofFn] using hi')
  have hprefix : Ideal.ofList ((List.ofFn fun j => f (s j)).take i) =
      Ideal.ofList ((List.ofFn fun j => g (s j)).take i) := by
    simpa only [List.map_take, List.map_ofFn, Function.comp_def] using
      hList ((List.ofFn s).take i)
  change IsSMulRegular (T ⧸
    (Ideal.ofList ((List.ofFn fun j => f (s j)).take i) • ⊤ : Submodule T T))
      ((List.ofFn fun j => f (s j))[i])
  rw [hprefix]
  simp only [List.getElem_ofFn] at hw ⊢
  have hm : g (s ⟨i, hi'⟩) ∈ Ideal.span {f (s ⟨i, hi'⟩)} :=
    (hspan _).symm ▸ Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hm
  intro x y hxy
  apply hw
  change g (s ⟨i, hi'⟩) • x = g (s ⟨i, hi'⟩) • y
  change f (s ⟨i, hi'⟩) • x = f (s ⟨i, hi'⟩) • y at hxy
  rw [hc, mul_comm, mul_smul, mul_smul, hxy]

/-- 同じ実評価有限族は、通常商のKoszul分解を与える。 -/
theorem deltaDivisionMappedNextEvaluation_fin_isKoszulResolution {m : ℕ} (s : Fin m → σ)
    (hr : RingTheory.Sequence.IsWeaklyRegular T (List.ofFn fun i =>
      q (deltaDivisionIteratedRelation D d a (s i) (N + 1)))) :
    SerrePositivity.IsKoszulResolution (fun i =>
      q (deltaDivisionEvaluationRelation D d a (s i) (N + 1))) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaDivisionMappedNextEvaluation_fin_isWeaklyRegular D d a q N hI s hr)

end SerrePositivity.BhattScholze

end DeltaDivisionEvaluationFamilyStep

/-! ## 部分根族と補集合の自由δ変数の分離 -/

@[expose] public noncomputable section RelativeFreeSubsetSplit

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (T : Set σ)

/-- 各δ深さを保って、部分根族と補集合の座標を分ける添字同値。 -/
def relativeFreeSubsetVariableSplit :
    σ × ℕ ≃ (T × ℕ) ⊕ ((Tᶜ : Set σ) × ℕ) := by
  classical
  exact (Equiv.prodCongr (Equiv.Set.sumCompl T).symm (Equiv.refl ℕ)).trans
    (Equiv.sumProdDistrib T (Tᶜ : Set σ) ℕ)

/-- 部分根族の座標は外側の多項式変数へ送られる。 -/
@[simp] theorem relativeFreeSubsetVariableSplit_mem (s : T) (n : ℕ) :
    relativeFreeSubsetVariableSplit T (s, n) = Sum.inl (s, n) := by
  classical
  simp [relativeFreeSubsetVariableSplit]

/-- 補集合の座標は係数側の多項式変数へ送られる。 -/
@[simp] theorem relativeFreeSubsetVariableSplit_compl (s : (Tᶜ : Set σ)) (n : ℕ) :
    relativeFreeSubsetVariableSplit T (s, n) = Sum.inr (s, n) := by
  classical
  simp [relativeFreeSubsetVariableSplit]

local notation "B" => RelativeFreeDeltaRing (R := A) (Tᶜ : Set σ)
local notation "C" => RelativeFreeDeltaRing (R := B) T

/-- 補集合の自由δ環を係数にすると、元の自由環は部分根族の相対自由環となる。 -/
def relativeFreeSubsetSplitAlgEquiv : RelativeFreeDeltaRing (R := A) σ ≃ₐ[A] C :=
  (MvPolynomial.renameEquiv A (relativeFreeSubsetVariableSplit T)).trans
    (MvPolynomial.sumAlgEquiv A (T × ℕ) ((Tᶜ : Set σ) × ℕ))

/-- 分離同型は元の係数を二重の係数射へ送る。 -/
@[simp] theorem relativeFreeSubsetSplitAlgEquiv_C (a : A) :
    relativeFreeSubsetSplitAlgEquiv (A := A) T (MvPolynomial.C a) =
      MvPolynomial.C (MvPolynomial.C a) := by
  simp [relativeFreeSubsetSplitAlgEquiv]

/-- 部分根族の全δ座標は外側の座標となる。 -/
@[simp] theorem relativeFreeSubsetSplitAlgEquiv_X_mem (s : T) (n : ℕ) :
    relativeFreeSubsetSplitAlgEquiv (A := A) T (MvPolynomial.X ((s : σ), n)) =
      MvPolynomial.X (s, n) := by
  simp [relativeFreeSubsetSplitAlgEquiv]

/-- 補集合の全δ座標は係数環の座標となる。 -/
@[simp] theorem relativeFreeSubsetSplitAlgEquiv_X_compl (s : (Tᶜ : Set σ)) (n : ℕ) :
    relativeFreeSubsetSplitAlgEquiv (A := A) T (MvPolynomial.X ((s : σ), n)) =
      MvPolynomial.C (MvPolynomial.X (s, n)) := by
  simp [relativeFreeSubsetSplitAlgEquiv]

variable (D : DeltaStructure p A)
local notation "E" => relativeFreeDeltaStructure σ D
local notation "F" => relativeFreeDeltaStructure (Tᶜ : Set σ) D
local notation "G" => relativeFreeDeltaStructure T F
local notation "e" => relativeFreeSubsetSplitAlgEquiv (A := A) T

/-- 全δ深さを保つ部分族分離は、既存の二つの自由δ構造と両立する。 -/
theorem relativeFreeSubsetSplitAlgEquiv_isDeltaHom :
    (E).IsDeltaHom G (e).toRingHom := by
  apply DeltaStructure.isDeltaHom_mvPolynomial
  · intro a
    change e ((E).delta (MvPolynomial.C a)) = (G).delta (e (MvPolynomial.C a))
    simp
  · rintro ⟨s, n⟩
    change e ((E).delta (MvPolynomial.X (s, n))) = (G).delta (e (MvPolynomial.X (s, n)))
    by_cases hs : s ∈ T
    · have h (k : ℕ) := relativeFreeSubsetSplitAlgEquiv_X_mem (A := A) T ⟨s, hs⟩ k
      simp only [relativeFreeDeltaStructure_delta_X, h]
    · have h (k : ℕ) := relativeFreeSubsetSplitAlgEquiv_X_compl (A := A) T ⟨s, hs⟩ k
      simp only [relativeFreeDeltaStructure_delta_X, h, relativeFreeDeltaStructure_delta_C]

/-- 同じ分離同型の逆方向もδ構造を保つ。 -/
theorem relativeFreeSubsetSplitAlgEquiv_symm_isDeltaHom :
    (G).IsDeltaHom E (e).symm.toRingHom :=
  (relativeFreeSubsetSplitAlgEquiv_isDeltaHom T D).symm

/-- 部分族内の元の反復δ関係は、補集合を係数にした同じ反復関係へ送られる。 -/
theorem relativeFreeSubsetSplitAlgEquiv_iteratedRelation (d : A) (a : σ → A)
    (s : T) (n : ℕ) :
    e (deltaDivisionIteratedRelation D d a (s : σ) n) =
      deltaDivisionIteratedRelation F (MvPolynomial.C d)
        (fun t : T => MvPolynomial.C (a t)) s n := by
  induction n with
  | zero =>
    change e (MvPolynomial.C d * MvPolynomial.X ((s : σ), 0) - MvPolynomial.C (a s)) = _
    simp [deltaDivisionIteratedRelation]
  | succ n ih =>
    have h := relativeFreeSubsetSplitAlgEquiv_isDeltaHom T D
      (deltaDivisionIteratedRelation D d a (s : σ) n)
    change e ((E).delta (deltaDivisionIteratedRelation D d a (s : σ) n)) =
      (G).delta (e (deltaDivisionIteratedRelation D d a (s : σ) n)) at h
    have h' := h.trans (congrArg (G).delta ih)
    simpa only [deltaDivisionIteratedRelation, Function.iterate_succ_apply'] using h'

/-- 部分根族の有限深さ関係イデアルは、係数拡大後の既存有限関係イデアルへ移る。 -/
theorem relativeFreeSubsetSplitAlgEquiv_map_finiteRelations
    (d : A) (a : σ → A) (N : ℕ) :
    (Ideal.span (Set.range fun z : T × Fin (N + 1) =>
      deltaDivisionIteratedRelation D d a (z.1 : σ) z.2.val)).map (e).toRingHom =
        deltaDivisionFiniteRelationIdeal F (MvPolynomial.C d)
          (fun t : T => MvPolynomial.C (a t)) N := by
  rw [Ideal.map_span, ← Set.range_comp']
  change Ideal.span (Set.range fun z : T × Fin (N + 1) =>
    e (deltaDivisionIteratedRelation D d a (z.1 : σ) z.2.val)) = _
  unfold deltaDivisionFiniteRelationIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext z
  exact relativeFreeSubsetSplitAlgEquiv_iteratedRelation T D d a z.1 z.2.val

omit [Fact p.Prime] in
/-- 元のmod(p,d)係数イデアルも、同じ分離同型の下で標準係数イデアルへ移る。 -/
theorem relativeFreeSubsetSplitAlgEquiv_map_pd (d : A) :
    (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d}).map
        (e).toRingHom =
      Ideal.span {(p : C), MvPolynomial.C (MvPolynomial.C d)} := by
  rw [Ideal.map_span]
  simp only [Set.image_pair, map_natCast]
  change Ideal.span {(p : C), e (MvPolynomial.C d)} = _
  rw [relativeFreeSubsetSplitAlgEquiv_C]

/-- 部分根族の実有限深さmod(p,d)商は、補集合を係数とする同じ有限関係商。 -/
def relativeFreeSubsetFiniteResidueQuotientEquiv (d : A) (a : σ → A) (N : ℕ) :
    (RelativeFreeDeltaRing (R := A) σ ⧸
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        Ideal.span (Set.range fun z : T × Fin (N + 1) =>
          deltaDivisionIteratedRelation D d a (z.1 : σ) z.2.val))) ≃+*
    (C ⧸ (Ideal.span {(p : C), MvPolynomial.C (MvPolynomial.C d)} ⊔
      deltaDivisionFiniteRelationIdeal F (MvPolynomial.C d)
        (fun t : T => MvPolynomial.C (a t)) N)) :=
  Ideal.quotientEquiv _ _ (e).toRingEquiv (by
    change _ = Ideal.map (e).toRingHom _
    rw [Ideal.map_sup, relativeFreeSubsetSplitAlgEquiv_map_pd,
      relativeFreeSubsetSplitAlgEquiv_map_finiteRelations])

end SerrePositivity.BhattScholze

end RelativeFreeSubsetSplit

/-! ## 自由δ射の両因子の係数商に沿うTor消滅

係数射の平坦性と具体的な係数上の式を共通のTor基底変更へ供給する。
係数イデアルの正則性・完備性や余極限との比較は要求しない。
-/

@[expose] public noncomputable section DeltaDivisionSourceCoefficientTor

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ

omit [Fact p.Prime] in
/-- 自由δ環での(p,Cd)イデアルは元の係数イデアル(p,d)の拡張。 -/
theorem deltaDivisionSourceCoefficientIdeal_map (d : A) :
    (Ideal.span {(p : A), d}).map (MvPolynomial.C : A →+* P₀) =
      Ideal.span {(p : P₀), MvPolynomial.C d} := by
  rw [Ideal.map_span]
  simp only [Set.image_pair, map_natCast]

/-- 任意の係数商に沿う、実評価βで作用するAの高次Torは零。 -/
theorem deltaDivisionSourceEvaluation_coefficientTorVanishing
    (D : DeltaStructure p A) (a : σ → A) (I : Ideal A) :
    scalarExtensionTorVanishing
      (Ideal.Quotient.mk (I.map (MvPolynomial.C : A →+* P₀)))
      (baseChangeScalarModule (deltaDivisionSourceEval D a)) := by
  let := deltaDivisionSourceEvaluationAlgebra D a
  have hC : (MvPolynomial.C : A →+* P₀).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have hcomp : (algebraMap P₀ A).comp (MvPolynomial.C : A →+* P₀) = RingHom.id A := by
    apply RingHom.ext
    intro r
    exact deltaDivisionSourceEval_C D a r
  have hA : ((algebraMap P₀ A).comp (MvPolynomial.C : A →+* P₀)).Flat := by
    rw [hcomp]
    exact RingHom.Flat.id A
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
      let q := Ideal.Quotient.mk (I.map (MvPolynomial.C : A →+* P₀))
      let Mβ := baseChangeScalarModule (deltaDivisionSourceEval D a)
      let Mq := baseChangeScalarModule q
      let : Subsingleton (TorModule P₀ (n + 1) A (P₀ ⧸ I.map MvPolynomial.C)) :=
        torModule_quotient_map_subsingleton (MvPolynomial.C : A →+* P₀) hC A hA I n
      let eT : Mβ ≃ₗ[P₀] A :=
        { toFun := fun z => z
          invFun := fun z => z
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let eQ : Mq ≃ₗ[P₀] (P₀ ⧸ I.map MvPolynomial.C) :=
        { toFun := fun z => z
          invFun := fun z => z
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := by
            intro r z
            obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
            rfl }
      let e : (((Tor (ModuleCat P₀) (n + 1)).obj Mβ).obj Mq) ≅
          (((Tor (ModuleCat P₀) (n + 1)).obj (ModuleCat.of P₀ A)).obj
            (ModuleCat.of P₀ (P₀ ⧸ I.map MvPolynomial.C))) :=
        ((Tor (ModuleCat P₀) (n + 1)).mapIso eT.toModuleIso).app Mq ≪≫
          ((Tor (ModuleCat P₀) (n + 1)).obj (ModuleCat.of P₀ A)).mapIso eQ.toModuleIso
      let : Subsingleton (TorModule P₀ (n + 1) Mβ Mq) :=
        e.toLinearEquiv.injective.subsingleton
      have hs : Subsingleton (TorModule P₀ (n + 1) Mq Mβ) :=
        (torComm (n + 1) Mq Mβ).injective.subsingleton
      exact ModuleCat.isZero_iff_subsingleton.mpr hs

/-- 任意の係数商に沿う、実自由δ射αで作用する終域の高次Torは零。 -/
theorem deltaDivisionSourceTarget_coefficientTorVanishing
    (D : DeltaStructure p A) (d : A) (I : Ideal A) :
    scalarExtensionTorVanishing
      (Ideal.Quotient.mk (I.map (MvPolynomial.C : A →+* P₀)))
      (baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)) := by
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  have hC : (MvPolynomial.C : A →+* P₀).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have hcomp : (algebraMap P₀ P₀).comp (MvPolynomial.C : A →+* P₀) =
      (MvPolynomial.C : A →+* P₀) := by
    apply RingHom.ext
    intro r
    exact deltaDivisionSourceMap_C D d r
  have hP : ((algebraMap P₀ P₀).comp (MvPolynomial.C : A →+* P₀)).Flat := by
    rw [hcomp]
    exact hC
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
      let q := Ideal.Quotient.mk (I.map (MvPolynomial.C : A →+* P₀))
      let Mα := baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)
      let Mq := baseChangeScalarModule q
      let : Subsingleton (TorModule P₀ (n + 1) P₀ (P₀ ⧸ I.map MvPolynomial.C)) :=
        torModule_quotient_map_subsingleton (MvPolynomial.C : A →+* P₀) hC P₀ hP I n
      let eT : Mα ≃ₗ[P₀] P₀ :=
        { toFun := fun z => z
          invFun := fun z => z
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let eQ : Mq ≃ₗ[P₀] (P₀ ⧸ I.map MvPolynomial.C) :=
        { toFun := fun z => z
          invFun := fun z => z
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := by
            intro r z
            obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
            rfl }
      let e : (((Tor (ModuleCat P₀) (n + 1)).obj Mα).obj Mq) ≅
          (((Tor (ModuleCat P₀) (n + 1)).obj (ModuleCat.of P₀ P₀)).obj
            (ModuleCat.of P₀ (P₀ ⧸ I.map MvPolynomial.C))) :=
        ((Tor (ModuleCat P₀) (n + 1)).mapIso eT.toModuleIso).app Mq ≪≫
          ((Tor (ModuleCat P₀) (n + 1)).obj (ModuleCat.of P₀ P₀)).mapIso eQ.toModuleIso
      let : Subsingleton (TorModule P₀ (n + 1) Mα Mq) :=
        e.toLinearEquiv.injective.subsingleton
      have hs : Subsingleton (TorModule P₀ (n + 1) Mq Mα) :=
        (torComm (n + 1) Mq Mα).injective.subsingleton
      exact ModuleCat.isZero_iff_subsingleton.mpr hs

end SerrePositivity.BhattScholze

end DeltaDivisionSourceCoefficientTor

/-! ## 自由δ射の両因子を伴う実係数商基底変更

共通の実導来テンソル商比較へ、証明済みの両因子のTor消滅を供給する。
残余環を係数側Koszul複体と同一視したり、完備化後CFFを結論したりしない。
-/

@[expose] public noncomputable section DeltaDivisionSourceCoefficientReduction

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (I : Ideal A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "J₀" => I.map (MvPolynomial.C : A →+* P₀)
local notation "q₀" => Ideal.Quotient.mk J₀
local notation "Mβ" => baseChangeScalarModule (deltaDivisionSourceEval D a)
local notation "Mα" => baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)

/-- β側の係数イデアル像は、元の係数イデアルIそのもの。 -/
theorem deltaDivisionSourceEvaluation_coefficientIdeal_map :
    (J₀).map (deltaDivisionSourceEval D a) = I := by
  rw [Ideal.map_map]
  have h : (deltaDivisionSourceEval D a).comp (MvPolynomial.C : A →+* P₀) =
      RingHom.id A := by
    apply RingHom.ext
    intro r
    exact deltaDivisionSourceEval_C D a r
  rw [h, Ideal.map_id]

/-- α側の係数イデアル像は同じ拡張イデアル。ただしαの源作用を保つ。 -/
theorem deltaDivisionSourceTarget_coefficientIdeal_map :
    (J₀).map (deltaDivisionSourceMap (σ := σ) D d) = J₀ := by
  rw [Ideal.map_map]
  have h : (deltaDivisionSourceMap (σ := σ) D d).comp (MvPolynomial.C : A →+* P₀) =
      (MvPolynomial.C : A →+* P₀) := by
    apply RingHom.ext
    intro r
    exact deltaDivisionSourceMap_C D d r
  rw [h]

/-- 実自由δ射の両因子のテンソルを係数商で実導来還元する標準比較。
両因子のTor仮定は既存の平坦基底変更から証明済みの補題で供給する。 -/
def deltaDivisionSourceCoefficientReductionIso :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    boundedAboveDerivedTensor.obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ A),
            boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ P₀)),
          derivedBaseChangeScalarObject q₀) ≅
      (boundedAboveDerivedRestrictScalars q₀).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj
            (ModuleCat.of (P₀ ⧸ J₀) (A ⧸ (J₀).map (algebraMap P₀ A))),
           boundedAboveDerivedSingleFunctor.obj
            (ModuleCat.of (P₀ ⧸ J₀) (P₀ ⧸ (J₀).map (algebraMap P₀ P₀))))) := by
  letI := deltaDivisionSourceEvaluationAlgebra D a
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  exact restrictedDerivedTensorQuotientAlgebraIso J₀ A P₀
    (deltaDivisionSourceEvaluation_coefficientTorVanishing D a I)
    (deltaDivisionSourceTarget_coefficientTorVanishing D d I)

/-- 同じ両因子の比較を、実係数拡大の値そのものを用いる加群表示で与える。 -/
def deltaDivisionSourceCoefficientModuleReductionIso :
    boundedAboveDerivedTensor.obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα),
          derivedBaseChangeScalarObject q₀) ≅
      (boundedAboveDerivedRestrictScalars q₀).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars q₀).obj Mβ),
            boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars q₀).obj Mα))) :=
  ((boundedAboveDerivedBaseChangeRightTensorNatIso q₀).app _).symm ≪≫
    (boundedAboveDerivedRestrictScalars q₀).mapIso
      (boundedAboveDerivedTensorBaseChangeModuleIso q₀ Mβ Mα
        (deltaDivisionSourceEvaluation_coefficientTorVanishing D a I)
        (deltaDivisionSourceTarget_coefficientTorVanishing D d I))

end SerrePositivity.BhattScholze

end DeltaDivisionSourceCoefficientReduction

/-! ## 自由δ射の係数商への標準降下

任意の係数イデアルを扱い、商のδ構造は要求しない。
自由δ射の商への降下と標準自己射を区別する。
-/

@[expose] public noncomputable section DeltaDivisionSourceCoefficientMaps

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (I : Ideal A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "J₀" => I.map (MvPolynomial.C : A →+* P₀)
local notation "Q₀" => P₀ ⧸ J₀
local notation "β₀" => deltaDivisionSourceEval D a
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D d

/-- 実評価βの係数商への標準降下。 -/
def deltaDivisionSourceCoefficientEvalMap : Q₀ →+* A ⧸ I :=
  Ideal.quotientMap I β₀ (Ideal.map_le_iff_le_comap.mp
    (le_of_eq (deltaDivisionSourceEvaluation_coefficientIdeal_map D a I)))

/-- 実自由δ射αの係数商への標準降下。 -/
def deltaDivisionSourceCoefficientTargetMap : Q₀ →+* Q₀ :=
  Ideal.quotientMap J₀ α₀ (Ideal.map_le_iff_le_comap.mp
    (le_of_eq (deltaDivisionSourceTarget_coefficientIdeal_map (σ := σ) D d I)))

/-- 係数包含の商への標準降下。 -/
def deltaDivisionSourceCoefficientBaseMap : A ⧸ I →+* Q₀ :=
  Ideal.quotientMap J₀ (MvPolynomial.C : A →+* P₀)
    (Ideal.map_le_iff_le_comap.mp le_rfl)

/-- βの降下は、標準商代表元の実評価で与えられる。 -/
theorem deltaDivisionSourceCoefficientEvalMap_mk (r : P₀) :
    deltaDivisionSourceCoefficientEvalMap D a I (Ideal.Quotient.mk J₀ r) =
      Ideal.Quotient.mk I (β₀ r) :=
  Ideal.quotientMap_mk

/-- αの降下は、標準商代表元の実自由δ像で与えられる。 -/
theorem deltaDivisionSourceCoefficientTargetMap_mk (r : P₀) :
    deltaDivisionSourceCoefficientTargetMap (σ := σ) D d I (Ideal.Quotient.mk J₀ r) =
      Ideal.Quotient.mk J₀ (α₀ r) :=
  Ideal.quotientMap_mk

/-- 係数包含の降下は、係数の標準商像を保つ。 -/
theorem deltaDivisionSourceCoefficientBaseMap_mk (r : A) :
    deltaDivisionSourceCoefficientBaseMap (σ := σ) I (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk J₀ (MvPolynomial.C r) :=
  Ideal.quotientMap_mk

/-- βの標準降下の商射との可換図式。 -/
theorem deltaDivisionSourceCoefficientEvalMap_comp_quotient :
    (deltaDivisionSourceCoefficientEvalMap D a I).comp (Ideal.Quotient.mk J₀) =
      (Ideal.Quotient.mk I).comp β₀ := by
  apply RingHom.ext
  intro r
  exact deltaDivisionSourceCoefficientEvalMap_mk D a I r

/-- αの標準降下の商射との可換図式。 -/
theorem deltaDivisionSourceCoefficientTargetMap_comp_quotient :
    (deltaDivisionSourceCoefficientTargetMap (σ := σ) D d I).comp (Ideal.Quotient.mk J₀) =
      (Ideal.Quotient.mk J₀).comp α₀ := by
  apply RingHom.ext
  intro r
  exact deltaDivisionSourceCoefficientTargetMap_mk D d I r

/-- 商への降下後も、実評価は係数包含の左逆。 -/
theorem deltaDivisionSourceCoefficientEvalMap_comp_base :
    (deltaDivisionSourceCoefficientEvalMap D a I).comp
      (deltaDivisionSourceCoefficientBaseMap (σ := σ) I) = RingHom.id (A ⧸ I) := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  change deltaDivisionSourceCoefficientEvalMap D a I
    (deltaDivisionSourceCoefficientBaseMap (σ := σ) I (Ideal.Quotient.mk I r)) = _
  rw [deltaDivisionSourceCoefficientBaseMap_mk, deltaDivisionSourceCoefficientEvalMap_mk,
    deltaDivisionSourceEval_C]
  rfl

/-- 商へ降下した自由δ射は係数包含を固定する。自己射と同一視はしない。 -/
theorem deltaDivisionSourceCoefficientTargetMap_comp_base :
    (deltaDivisionSourceCoefficientTargetMap (σ := σ) D d I).comp
      (deltaDivisionSourceCoefficientBaseMap (σ := σ) I) =
        deltaDivisionSourceCoefficientBaseMap (σ := σ) I := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  change deltaDivisionSourceCoefficientTargetMap D d I
    (deltaDivisionSourceCoefficientBaseMap (σ := σ) I (Ideal.Quotient.mk I r)) = _
  rw [deltaDivisionSourceCoefficientBaseMap_mk, deltaDivisionSourceCoefficientTargetMap_mk,
    deltaDivisionSourceMap_C]
  rfl

end SerrePositivity.BhattScholze

end DeltaDivisionSourceCoefficientMaps

/-! ## 実係数商還元の両因子と降下作用の明示

商イデアルの一致だけで作用を省略せず、βbar・αbarの作用を持つ標準商と比較する。
-/

@[expose] public noncomputable section DeltaDivisionSourceCoefficientQuotients

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (I : Ideal A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "J₀" => I.map (MvPolynomial.C : A →+* P₀)
local notation "Q₀" => P₀ ⧸ J₀
local notation "β₀" => deltaDivisionSourceEval D a
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D d

/-- βbarが定める実評価係数商の源商代数構造。 -/
@[instance_reducible] def deltaDivisionSourceCoefficientEvalAlgebra : Algebra Q₀ (A ⧸ I) :=
  (deltaDivisionSourceCoefficientEvalMap D a I).toAlgebra

/-- αbarが定める実終域係数商の源商代数構造。 -/
@[instance_reducible] def deltaDivisionSourceCoefficientTargetAlgebra : Algebra Q₀ Q₀ :=
  (deltaDivisionSourceCoefficientTargetMap (σ := σ) D d I).toAlgebra

/-- β側の通常商を、βbarの実源作用を保ってA/Iと比較する。 -/
def deltaDivisionSourceCoefficientEvalQuotientAlgEquiv :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    letI : Algebra Q₀ (A ⧸ (J₀).map β₀) := adicQuotientAlgebra J₀ A
    letI := deltaDivisionSourceCoefficientEvalAlgebra D a I
    (A ⧸ (J₀).map β₀) ≃ₐ[Q₀] (A ⧸ I) := by
  letI := deltaDivisionSourceEvaluationAlgebra D a
  letI : Algebra Q₀ (A ⧸ (J₀).map β₀) := adicQuotientAlgebra J₀ A
  letI := deltaDivisionSourceCoefficientEvalAlgebra D a I
  apply AlgEquiv.ofRingEquiv
    (f := Ideal.quotEquivOfEq (deltaDivisionSourceEvaluation_coefficientIdeal_map D a I))
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.quotEquivOfEq _ (Ideal.Quotient.mk ((J₀).map β₀) (β₀ r)) =
    deltaDivisionSourceCoefficientEvalMap D a I (Ideal.Quotient.mk J₀ r)
  rw [Ideal.quotEquivOfEq_mk, deltaDivisionSourceCoefficientEvalMap_mk]

/-- α側の通常商を、αbarの実源作用を保ってL/Jと比較する。 -/
def deltaDivisionSourceCoefficientTargetQuotientAlgEquiv :
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    letI : Algebra Q₀ (P₀ ⧸ (J₀).map α₀) := adicQuotientAlgebra J₀ P₀
    letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
    letI : Module Q₀ Q₀ := Algebra.toModule
    (P₀ ⧸ (J₀).map α₀) ≃ₐ[Q₀] Q₀ := by
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  letI : Algebra Q₀ (P₀ ⧸ (J₀).map α₀) := adicQuotientAlgebra J₀ P₀
  letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
  letI : Module Q₀ Q₀ := Algebra.toModule
  apply AlgEquiv.ofRingEquiv
    (f := Ideal.quotEquivOfEq (deltaDivisionSourceTarget_coefficientIdeal_map (σ := σ) D d I))
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.quotEquivOfEq _ (Ideal.Quotient.mk ((J₀).map α₀) (α₀ r)) =
    deltaDivisionSourceCoefficientTargetMap (σ := σ) D d I (Ideal.Quotient.mk J₀ r)
  rw [Ideal.quotEquivOfEq_mk, deltaDivisionSourceCoefficientTargetMap_mk]

/-- 実二因子導来還元の右辺を、βbarで作用するA/Iとαbarで作用するL/Jで明示する。 -/
def deltaDivisionSourceCoefficientExplicitReductionIso :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    letI : Algebra Q₀ (A ⧸ (J₀).map β₀) := adicQuotientAlgebra J₀ A
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    letI : Algebra Q₀ (P₀ ⧸ (J₀).map α₀) := adicQuotientAlgebra J₀ P₀
    letI := deltaDivisionSourceCoefficientEvalAlgebra D a I
    letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
    letI : Module Q₀ Q₀ := Algebra.toModule
    boundedAboveDerivedTensor.obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ A),
            boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ P₀)),
          derivedBaseChangeScalarObject (Ideal.Quotient.mk J₀)) ≅
      (boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk J₀)).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ (A ⧸ I)),
            boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Q₀))) := by
  letI := deltaDivisionSourceEvaluationAlgebra D a
  letI : Algebra Q₀ (A ⧸ (J₀).map β₀) := adicQuotientAlgebra J₀ A
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  letI : Algebra Q₀ (P₀ ⧸ (J₀).map α₀) := adicQuotientAlgebra J₀ P₀
  letI := deltaDivisionSourceCoefficientEvalAlgebra D a I
  letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
  letI : Module Q₀ Q₀ := Algebra.toModule
  let eβ := (deltaDivisionSourceCoefficientEvalQuotientAlgEquiv D a I).toLinearEquiv.toModuleIso
  let eα :=
    (deltaDivisionSourceCoefficientTargetQuotientAlgEquiv (σ := σ) D d I).toLinearEquiv.toModuleIso
  exact deltaDivisionSourceCoefficientReductionIso D d a I ≪≫
    (boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk J₀)).mapIso
      (boundedAboveDerivedTensor.mapIso
        (Iso.prod (boundedAboveDerivedSingleFunctor.mapIso eβ)
          (boundedAboveDerivedSingleFunctor.mapIso eα)))

end SerrePositivity.BhattScholze

end DeltaDivisionSourceCoefficientQuotients

/-! ## 係数商還元を右因子へ移す実導来比較

共通の結合子と右係数拡大比較を使い、証明済みのα因子のTor消滅を供給する。
-/

@[expose] public noncomputable section DeltaDivisionSourceCoefficientRightFactor

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (I : Ideal A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "J₀" => I.map (MvPolynomial.C : A →+* P₀)
local notation "Q₀" => P₀ ⧸ J₀
local notation "q₀" => Ideal.Quotient.mk J₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) D d
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule (deltaDivisionSourceEval D a)
local notation "Mψ" => baseChangeScalarModule ψ₀

/-- 商へ降下したαbarの作用を係数制限すると、ψ=q∘αの実作用になる。 -/
def deltaDivisionSourceCoefficientTargetRestrictedScalarEquiv :
    letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
    letI : Module Q₀ Q₀ := Algebra.toModule
    (ModuleCat.restrictScalars q₀).obj (ModuleCat.of Q₀ Q₀) ≃ₗ[P₀] Mψ := by
  letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
  letI : Module Q₀ Q₀ := Algebra.toModule
  exact
    { toFun := fun z => z
      invFun := fun z => z
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r z
        change deltaDivisionSourceCoefficientTargetMap D d I (q₀ r) * (show Q₀ from z) =
          ψ₀ r * (show Q₀ from z)
        rw [deltaDivisionSourceCoefficientTargetMap_mk]
        rfl }

/-- α因子の実導来係数拡大は、αbarの作用を持つ実商の次数零対象。 -/
def deltaDivisionSourceCoefficientTargetDerivedIso :
    letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
    letI : Module Q₀ Q₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).obj (boundedAboveDerivedSingleFunctor.obj Mα) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Q₀) := by
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  letI : Algebra Q₀ (P₀ ⧸ (J₀).map α₀) := adicQuotientAlgebra J₀ P₀
  letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
  letI : Module Q₀ Q₀ := Algebra.toModule
  exact derivedQuotientAlgebraIso J₀ P₀
    (deltaDivisionSourceTarget_coefficientTorVanishing (σ := σ) D d I) ≪≫
      boundedAboveDerivedSingleFunctor.mapIso
        (deltaDivisionSourceCoefficientTargetQuotientAlgEquiv
          (σ := σ) D d I).toLinearEquiv.toModuleIso

/-- 実導来α因子を商から係数制限すると、実残余射ψの次数零加群に一致する。 -/
def deltaDivisionSourceCoefficientTargetRestrictedIso :
    (boundedAboveDerivedRestrictScalars q₀).obj
      ((boundedAboveDerivedBaseChange q₀).obj (boundedAboveDerivedSingleFunctor.obj Mα)) ≅
        boundedAboveDerivedSingleFunctor.obj Mψ := by
  letI := deltaDivisionSourceCoefficientTargetAlgebra (σ := σ) D d I
  letI : Module Q₀ Q₀ := Algebra.toModule
  let e₁ := (boundedAboveDerivedRestrictScalars q₀).mapIso
    (deltaDivisionSourceCoefficientTargetDerivedIso (σ := σ) D d I)
  let e₂ : (boundedAboveDerivedRestrictScalars q₀).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Q₀)) ≅
        boundedAboveDerivedSingleFunctor.obj
          ((ModuleCat.restrictScalars q₀).obj (ModuleCat.of Q₀ Q₀)) :=
    ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso q₀ 0).app (ModuleCat.of Q₀ Q₀))
  exact e₁ ≪≫ e₂ ≪≫ boundedAboveDerivedSingleFunctor.mapIso
    (deltaDivisionSourceCoefficientTargetRestrictedScalarEquiv (σ := σ) D d I).toModuleIso

/-- α因子と実係数商の右導来テンソルは、実残余射ψの次数零加群。 -/
def deltaDivisionSourceCoefficientRightTensorIso :
    boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj Mα, derivedBaseChangeScalarObject q₀) ≅
      boundedAboveDerivedSingleFunctor.obj Mψ :=
  ((boundedAboveDerivedBaseChangeRightTensorNatIso q₀).app
    (boundedAboveDerivedSingleFunctor.obj Mα)).symm ≪≫
      deltaDivisionSourceCoefficientTargetRestrictedIso (σ := σ) D d I

/-- 結合子を用い、二因子の実係数商還元を実残余右因子との導来テンソルへ移す。 -/
def deltaDivisionSourceCoefficientAssociatorReductionIso :
    boundedAboveDerivedTensor.obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα),
          derivedBaseChangeScalarObject q₀) ≅
      boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mψ) :=
  boundedAboveDerivedTensorAssociator _ _ _ ≪≫ boundedAboveDerivedTensor.mapIso
    (Iso.prod (Iso.refl _) (deltaDivisionSourceCoefficientRightTensorIso (σ := σ) D d I))

/-- (p,d)係数還元を、実商射L→L/(p,Cd)との合成作用を持つ右因子へ移す。 -/
def deltaDivisionSourceResidueAssociatorReductionIso :
    boundedAboveDerivedTensor.obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα),
          derivedBaseChangeScalarObject (Ideal.Quotient.mk
            (Ideal.span {(p : P₀), MvPolynomial.C d}))) ≅
      boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj Mβ,
          boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule
            ((Ideal.Quotient.mk (Ideal.span {(p : P₀), MvPolynomial.C d})).comp α₀))) := by
  have e := deltaDivisionSourceCoefficientAssociatorReductionIso D d a
    (Ideal.span {(p : A), d})
  let F := fun J : Ideal P₀ => boundedAboveDerivedTensor.obj
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα),
        derivedBaseChangeScalarObject (Ideal.Quotient.mk J)) ≅
      boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj Mβ,
          boundedAboveDerivedSingleFunctor.obj
            (baseChangeScalarModule ((Ideal.Quotient.mk J).comp α₀)))
  change F ((Ideal.span {(p : A), d}).map (MvPolynomial.C : A →+* P₀)) at e
  change F (Ideal.span {(p : P₀), MvPolynomial.C d})
  exact Eq.mp (congrArg F (deltaDivisionSourceCoefficientIdeal_map (σ := σ) d)) e

end SerrePositivity.BhattScholze

end DeltaDivisionSourceCoefficientRightFactor

/-! ## 実通常テンソルのδ構造と両因子の標準包含

raw包のδ切断を標準比較同型とW₂写像で引き戻す。
-/

@[expose] public noncomputable section DeltaDivisionSourceTensorDelta

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} {σ : Type v} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (c : σ → A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "R₀" => TensorProduct P₀ A P₀
local notation "a₀" => c
local notation "B₀" => DeltaAdjoinDivision D d a₀

/-- 実通常テンソル上の、raw包の標準比較で引き戻した具体的δ構造。 -/
def deltaDivisionSourceTensorDelta :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    DeltaStructure p R₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  let e := deltaDivisionSourceTensorEquiv (σ := σ) D d c
  let E := deltaAdjoinDivisionStructure D d a₀
  exact E.comapEquiv e

/-- 実通常テンソルからraw包への標準環同型はδ構造を保存する。 -/
theorem deltaDivisionSourceTensorEquiv_isDeltaHom :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaDivisionSourceTensorDelta (σ := σ) D d c).IsDeltaHom
      (deltaAdjoinDivisionStructure D d a₀)
      (deltaDivisionSourceTensorEquiv D d c).toRingHom := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  let e := deltaDivisionSourceTensorEquiv (σ := σ) D d c
  let E := deltaAdjoinDivisionStructure D d a₀
  exact E.comapEquiv_isDeltaHom e

/-- raw包から実通常テンソルへの標準逆同型もδ構造を保存する。 -/
theorem deltaDivisionSourceTensorEquiv_symm_isDeltaHom :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaAdjoinDivisionStructure D d a₀).IsDeltaHom
      (deltaDivisionSourceTensorDelta (σ := σ) D d c)
      (deltaDivisionSourceTensorEquiv D d c).symm.toRingHom := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  exact (deltaDivisionSourceTensorEquiv_isDeltaHom (σ := σ) D d c).symm

/-- 通常テンソルの元の基底Aの標準包含はδ射。 -/
theorem deltaDivisionSourceTensor_includeLeft_isDeltaHom :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    D.IsDeltaHom (deltaDivisionSourceTensorDelta (σ := σ) D d c)
      Algebra.TensorProduct.includeLeftRingHom := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  have h := (deltaDivisionSourceTensorEquiv_symm_isDeltaHom (σ := σ) D d c).comp
    (deltaAdjoinDivisionMap_isDeltaHom D d a₀)
  change D.IsDeltaHom (deltaDivisionSourceTensorDelta (σ := σ) D d c)
    ((deltaDivisionSourceRawToTensor D d c).comp (deltaAdjoinDivisionMap D d a₀)) at h
  rw [deltaDivisionSourceRawToTensor_comp_base] at h
  exact h

/-- 通常テンソルの終域自由δ環Lの標準包含もδ射。 -/
theorem deltaDivisionSourceTensor_includeRight_isDeltaHom :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    (relativeFreeDeltaStructure σ D).IsDeltaHom (deltaDivisionSourceTensorDelta (σ := σ) D d c)
      Algebra.TensorProduct.includeRight.toRingHom := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  let E := relativeFreeDeltaStructure σ D
  let J := E.deltaClosure (deltaDivisionRelationIdeal d a₀)
  have hq := E.isDeltaHom_quotient_mk J (E.isStable_deltaClosure _)
  have h := (deltaDivisionSourceTensorEquiv_symm_isDeltaHom (σ := σ) D d c).comp hq
  change E.IsDeltaHom (deltaDivisionSourceTensorDelta (σ := σ) D d c)
    ((deltaDivisionSourceRawToTensor D d c).comp (Ideal.Quotient.mk J)) at h
  rw [deltaDivisionSourceRawToTensor_comp_quotient] at h
  exact h

/-- 両因子の標準包含をδ射にするδ構造は、構成したものに一意に一致する。 -/
theorem deltaDivisionSourceTensorDelta_unique :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    ∀ E : DeltaStructure p R₀,
      D.IsDeltaHom E Algebra.TensorProduct.includeLeftRingHom →
      (relativeFreeDeltaStructure σ D).IsDeltaHom E Algebra.TensorProduct.includeRight.toRingHom →
      E = deltaDivisionSourceTensorDelta (σ := σ) D d c := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  intro E hL hR
  let T := deltaDivisionSourceTensorDelta (σ := σ) D d c
  have hL' := deltaDivisionSourceTensor_includeLeft_isDeltaHom (σ := σ) D d c
  have hR' := deltaDivisionSourceTensor_includeRight_isDeltaHom (σ := σ) D d c
  have hLeft : E.sectionHom.comp Algebra.TensorProduct.includeLeftRingHom =
      T.sectionHom.comp Algebra.TensorProduct.includeLeftRingHom :=
    ((D.isDeltaHom_iff_sectionHom_comp E _).mp hL).symm.trans
      ((D.isDeltaHom_iff_sectionHom_comp T _).mp hL')
  have hRight : E.sectionHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      T.sectionHom.comp Algebra.TensorProduct.includeRight.toRingHom :=
    (((relativeFreeDeltaStructure σ D).isDeltaHom_iff_sectionHom_comp E _).mp hR).symm.trans
      (((relativeFreeDeltaStructure σ D).isDeltaHom_iff_sectionHom_comp T _).mp hR')
  have hs : E.sectionHom = T.sectionHom := Algebra.TensorProduct.ringHom_ext hLeft hRight
  apply DeltaStructure.ext
  intro r
  exact congrArg (fun z : WittTwo p R₀ => z.coeff 1) (RingHom.congr_fun hs r)

/-- 可換な二環射の自由δ因子側がδ射なら、通常pushoutからの延長も一意なδ射。
係数側のδ両立性は自由δ係数射と可換性から従うため追加仮定しない。 -/
theorem existsUnique_deltaDivisionSourceTensorDeltaHom {T : Type w} [CommRing T]
    (F : DeltaStructure p T) (f : A →+* T) (g : P₀ →+* T)
    (hg : (relativeFreeDeltaStructure σ D).IsDeltaHom F g)
    (h : g.comp (deltaDivisionSourceMap D d) = f.comp (deltaDivisionSourceEval D a₀)) :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    ∃! k : R₀ →+* T, (deltaDivisionSourceTensorDelta D d c).IsDeltaHom F k ∧
      k.comp Algebra.TensorProduct.includeLeftRingHom = f ∧
      k.comp Algebra.TensorProduct.includeRight.toRingHom = g := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  obtain ⟨k, hk, _⟩ := existsUnique_deltaDivisionSourceRawLift D d c f g h
  let J := (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d c)
  let q := Ideal.Quotient.mk J
  have hq : (relativeFreeDeltaStructure σ D).IsDeltaHom
      (deltaAdjoinDivisionStructure D d c) q :=
    (relativeFreeDeltaStructure σ D).isDeltaHom_quotient_mk J
      ((relativeFreeDeltaStructure σ D).isStable_deltaClosure _)
  have hkdelta : (deltaAdjoinDivisionStructure D d c).IsDeltaHom F k := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change k ((deltaAdjoinDivisionStructure D d c).delta (q r)) = F.delta (k (q r))
    rw [← hq r]
    have hk₀ := DFunLike.congr_fun hk.1 r
    have hk₁ := DFunLike.congr_fun hk.1 ((relativeFreeDeltaStructure σ D).delta r)
    change k (q r) = g r at hk₀
    change k (q ((relativeFreeDeltaStructure σ D).delta r)) = _ at hk₁
    rw [hk₁, hk₀]
    exact hg r
  let e := deltaDivisionSourceTensorEquiv D d c
  let l := k.comp e.toRingHom
  have hl : l.comp Algebra.TensorProduct.includeLeftRingHom = f := by
    apply RingHom.ext
    intro x
    change k (e (x ⊗ₜ[P₀] 1)) = f x
    rw [deltaDivisionSourceTensorEquiv_tmul, map_one, mul_one]
    exact DFunLike.congr_fun hk.2 x
  have hr : l.comp Algebra.TensorProduct.includeRight.toRingHom = g := by
    apply RingHom.ext
    intro r
    change k (e (1 ⊗ₜ[P₀] r)) = g r
    rw [deltaDivisionSourceTensorEquiv_tmul, map_one, one_mul]
    exact DFunLike.congr_fun hk.1 r
  refine ⟨l, ⟨hkdelta.comp (deltaDivisionSourceTensorEquiv_isDeltaHom D d c), hl, hr⟩, ?_⟩
  intro z hz
  exact Algebra.TensorProduct.ringHom_ext (hz.2.1.trans hl.symm) (hz.2.2.trans hr.symm)

end SerrePositivity.BhattScholze

end DeltaDivisionSourceTensorDelta
