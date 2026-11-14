module

public import SerrePositivity.BhattScholze.Delta.Basic.DeltaQuotient
public import SerrePositivity.BhattScholze.Delta.Division.Basic
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteDelta
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteTopVariable
public import Mathlib.Data.Finsupp.Weight

/-!
# δ 除算包の全反復関係式とその正規形

## 概要
δ 除算包を定める全反復関係式と、その有限多項式表示、最高変数の係数・次数・偏微分の p 剰余像、整係数での最高変数の分離、(p,d) 係数商・剰余での最高変数の除去と最高係数の消滅、第一 δ 除算関係式の二次誤差を含む正規形。
BS 著者版 Corollary 2.39 と Proposition 3.13 の包を調べるため、δ 除算の反復関係式を多項式で表示する。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Andre/Envelope/JetRegularity`、`Delta/DividedPower/PDivision`、`Delta/Division/Residue`、`Delta/Division/Source`、`Delta/Division/Witt`。
-/

universe u v w

/-! ## δ除算包の全反復関係式

δ閉包を、元の指定生成元の反復δ像だけによる通常イデアルとして表示する。
δ除算包の全段の関係式と変数を具体化する。三角形の次数評価は別工程。
-/

@[expose] public noncomputable section DeltaDivisionIteratedRelations

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

variable {σ : Type v}

/-- δ除算包の指定した全反復関係式。 -/
def deltaDivisionIteratedRelation (D : DeltaStructure p A) (d : A) (a : σ → A)
    (s : σ) (n : ℕ) : RelativeFreeDeltaRing (R := A) σ :=
  (relativeFreeDeltaStructure σ D).delta^[n]
    (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s))

/-- δ除算包の定義イデアルは、指定関係式の全反復δ像で生成される。 -/
theorem deltaDivision_deltaClosure_eq_span_iteratedRelations
    (D : DeltaStructure p A) (d : A) (a : σ → A) :
    (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a) =
      Ideal.span (Set.range fun z : σ × ℕ => deltaDivisionIteratedRelation D d a z.1 z.2) := by
  rw [deltaDivisionRelationIdeal,
    DeltaStructure.deltaClosure_span_eq_span_generator_iterates]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨n, _, ⟨s, rfl⟩, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨(s, n), rfl⟩
  · rintro ⟨⟨s, n⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨n, _, ⟨s, rfl⟩, rfl⟩

/-- 全反復関係式は実際のδ除算包で零になる。 -/
theorem deltaDivisionIteratedRelation_quotient_eq_zero
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
      (deltaDivisionRelationIdeal d a)) (deltaDivisionIteratedRelation D d a s n) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [deltaDivision_deltaClosure_eq_span_iteratedRelations]
  exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, n), rfl⟩)

/-- 相対自由δ環の反復δ変数は、全段の指定多項式変数と一致する。 -/
theorem relativeFreeDeltaStructure_iterate_delta_X
    (D : DeltaStructure p A) (s : σ) (n : ℕ) :
    (relativeFreeDeltaStructure σ D).delta^[n] (MvPolynomial.X (s, 0)) =
      MvPolynomial.X (s, n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, relativeFreeDeltaStructure_delta_X]

/-- 実際のδ除算包の初期変数の反復δ像は、全段変数の標準商像。 -/
theorem deltaAdjoinDivisionVariable_iterate_delta
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    (deltaAdjoinDivisionStructure D d a).delta^[n] (deltaAdjoinDivisionVariable D d a s) =
      Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal d a)) (MvPolynomial.X (s, n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact ((relativeFreeDeltaStructure σ D).isDeltaHom_quotient_mk _
        ((relativeFreeDeltaStructure σ D).isStable_deltaClosure _)
        (MvPolynomial.X (s, n))).symm.trans
          (congrArg (Ideal.Quotient.mk _) (relativeFreeDeltaStructure_delta_X σ D s n))

/-- 全反復関係式を消す通常の環射は、定義イデアル全体を消す。 -/
theorem deltaDivisionIteratedRelations_kill_ideal
    {B : Type*} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (f : RelativeFreeDeltaRing (R := A) σ →+* B)
    (hf : ∀ s n, f (deltaDivisionIteratedRelation D d a s n) = 0) :
    ∀ x ∈ (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a),
      f x = 0 := by
  have hle : (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a) ≤
      RingHom.ker f := by
    rw [deltaDivision_deltaClosure_eq_span_iteratedRelations]
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, n⟩, rfl⟩
    exact hf s n
  exact fun x hx => hle hx

/-- 全反復関係式を消す通常の環射から、δ除算包上の具体的な環射を構成する。
終域のδ構造を仮定しない。 -/
def deltaDivisionIteratedRelationsLift
    {B : Type*} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (f : RelativeFreeDeltaRing (R := A) σ →+* B)
    (hf : ∀ s n, f (deltaDivisionIteratedRelation D d a s n) = 0) :
    DeltaAdjoinDivision D d a →+* B :=
  Ideal.Quotient.lift _ f (deltaDivisionIteratedRelations_kill_ideal D d a f hf)

/-- 全関係式から構成した射と標準商射の図式。 -/
theorem deltaDivisionIteratedRelationsLift_comp_mk
    {B : Type*} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (f : RelativeFreeDeltaRing (R := A) σ →+* B)
    (hf : ∀ s n, f (deltaDivisionIteratedRelation D d a s n) = 0) :
    (deltaDivisionIteratedRelationsLift D d a f hf).comp
      (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal d a))) = f := rfl

/-- 全反復関係式を消す通常の環射は、δ除算包へ一意に降りる。 -/
theorem existsUnique_deltaDivisionIteratedRelationsLift
    {B : Type*} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A)
    (f : RelativeFreeDeltaRing (R := A) σ →+* B)
    (hf : ∀ s n, f (deltaDivisionIteratedRelation D d a s n) = 0) :
    ∃! L : DeltaAdjoinDivision D d a →+* B,
      L.comp (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal d a))) = f := by
  refine ⟨deltaDivisionIteratedRelationsLift D d a f hf, rfl, ?_⟩
  intro L hL
  exact Ideal.Quotient.ringHom_ext hL

/-- 深さN以下の反復関係式で生成した通常イデアル。
添字族σの有限性は仮定しない。 -/
def deltaDivisionFiniteRelationIdeal (D : DeltaStructure p A) (d : A) (a : σ → A)
    (N : ℕ) : Ideal (RelativeFreeDeltaRing (R := A) σ) :=
  Ideal.span (Set.range fun z : σ × Fin (N + 1) =>
    deltaDivisionIteratedRelation D d a z.1 z.2.val)

/-- 反復関係式の有限深さのイデアルは単調に増大する。 -/
theorem deltaDivisionFiniteRelationIdeal_mono
    (D : DeltaStructure p A) (d : A) (a : σ → A) :
    Monotone (deltaDivisionFiniteRelationIdeal D d a) := by
  intro N M hNM
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨s, n⟩, rfl⟩
  apply Ideal.subset_span
  exact Set.mem_range.mpr ⟨(s, ⟨n.val, lt_of_lt_of_le n.isLt (Nat.add_le_add_right hNM 1)⟩), rfl⟩

/-- 実際のδ閉包は、有限深さの関係式イデアルの上限。 -/
theorem deltaDivision_deltaClosure_eq_iSup_finiteRelations
    (D : DeltaStructure p A) (d : A) (a : σ → A) :
    (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a) =
      ⨆ N, deltaDivisionFiniteRelationIdeal D d a N := by
  rw [deltaDivision_deltaClosure_eq_span_iteratedRelations]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, n⟩, rfl⟩
    apply (le_iSup (deltaDivisionFiniteRelationIdeal D d a) n)
    exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, ⟨n, Nat.lt_succ_self n⟩), rfl⟩)
  · apply iSup_le
    intro N
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, n⟩, rfl⟩
    exact Ideal.subset_span (Set.mem_range.mpr ⟨(s, n.val), rfl⟩)

end SerrePositivity.BhattScholze

end DeltaDivisionIteratedRelations

/-! ## 全反復δ除算関係式の具体的な有限多項式表示

有限δ計算を反復し、深さnの関係式を初期n+1段に置く。
この段数制御だけからモニック性・平坦性は結論しない。
-/

@[expose] public noncomputable section DeltaDivisionFiniteRelationPolynomial

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 反復除算関係式を有限初期段で再帰的に計算した多項式。 -/
def deltaDivisionFiniteRelationPolynomial (D : DeltaStructure p A) (d : A) (a : σ → A)
    (s : σ) : (n : ℕ) → MvPolynomial (σ × Fin (n + 1)) A
  | 0 => MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s)
  | n + 1 => relativeFreeFiniteDeltaStep n σ D (deltaDivisionFiniteRelationPolynomial D d a s n)

/-- 深さ0の有限関係式は元の通常除算関係式。 -/
@[simp] theorem deltaDivisionFiniteRelationPolynomial_zero
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) :
    deltaDivisionFiniteRelationPolynomial D d a s 0 =
      MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s) := rfl

/-- 次の有限関係式は、一段大きい有限環でのδ計算。 -/
@[simp] theorem deltaDivisionFiniteRelationPolynomial_succ
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    deltaDivisionFiniteRelationPolynomial D d a s (n + 1) =
      relativeFreeFiniteDeltaStep n σ D (deltaDivisionFiniteRelationPolynomial D d a s n) := rfl

/-- 有限多項式の標準包含の像は、実際の全反復δ除算関係式に一致する。 -/
theorem deltaDivisionFiniteRelationPolynomial_image
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
      (deltaDivisionFiniteRelationPolynomial D d a s n) =
      deltaDivisionIteratedRelation D d a s n := by
  induction n with
  | zero =>
      simp [deltaDivisionFiniteRelationPolynomial, relativeFreeFiniteInitialPolynomialMap,
        deltaDivisionIteratedRelation]
  | succ n ih =>
      rw [deltaDivisionFiniteRelationPolynomial_succ,
        ← relativeFreeFiniteDeltaStep_delta_image, ih]
      exact (Function.iterate_succ_apply' (relativeFreeDeltaStructure σ D).delta n _).symm

/-- 深さnの実際の反復関係式には第n段までの変数しか現れない。 -/
theorem deltaDivisionIteratedRelation_variable_bound
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ)
    (z : σ × ℕ) (hz : z ∈ (deltaDivisionIteratedRelation D d a s n).vars) : z.2 ≤ n := by
  rw [← deltaDivisionFiniteRelationPolynomial_image D d a s n] at hz
  change z ∈ (MvPolynomial.rename (fun x : σ × Fin (n + 1) => (x.1, x.2.val))
    (deltaDivisionFiniteRelationPolynomial D d a s n)).vars at hz
  obtain ⟨⟨t, i⟩, _, he⟩ := MvPolynomial.mem_vars_rename _ _ hz
  have hn := i.isLt
  have hval := congrArg Prod.snd he
  change i.val = z.2 at hval
  omega

/-- 実際の反復関係式の有限初期多項式表示は一意。 -/
theorem deltaDivisionFiniteRelationPolynomial_unique
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ)
    (f : MvPolynomial (σ × Fin (n + 1)) A)
    (hf : relativeFreeFiniteInitialPolynomialMap (n + 1) σ A f =
      deltaDivisionIteratedRelation D d a s n) :
    f = deltaDivisionFiniteRelationPolynomial D d a s n :=
  relativeFreeFiniteInitialPolynomialMap_injective (n + 1) σ
    (hf.trans (deltaDivisionFiniteRelationPolynomial_image D d a s n).symm)

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteRelationPolynomial

/-! ## 実δ反復関係の整係数での最高変数分離

第n関係の最高変数は一次で係数φ^n(d)、残りは厳密に下のn段に属する。
p剰余への移行もpねじれの消去も使わない。
-/

@[expose] public noncomputable section DeltaDivisionFiniteLeadingLinear

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

private theorem initial_delta_exists (D : DeltaStructure p A) (n : ℕ)
    (b : MvPolynomial (σ × Fin n) A) :
    ∃ c : MvPolynomial (σ × Fin (n + 1)) A,
      (relativeFreeDeltaStructure σ D).delta
        (relativeFreeFiniteInitialPolynomialMap n σ A b) =
        relativeFreeFiniteInitialPolynomialMap (n + 1) σ A c := by
  cases n with
  | zero =>
      let e := MvPolynomial.isEmptyAlgEquiv A (σ × Fin 0)
      have hb : b = MvPolynomial.C (e b) := by
        simpa only [e, MvPolynomial.isEmptyAlgEquiv_symm_apply] using (e.symm_apply_apply b).symm
      refine ⟨MvPolynomial.C (D.delta (e b)), ?_⟩
      conv_lhs => rw [hb]
      simp [relativeFreeFiniteInitialPolynomialMap]
  | succ n =>
      exact ⟨relativeFreeFiniteDeltaStep n σ D b,
        relativeFreeFiniteDeltaStep_delta_image n σ D b⟩

private theorem affine_delta_exists (D : DeltaStructure p A) (c : A) (s : σ) (n : ℕ)
    (b : MvPolynomial (σ × Fin n) A) :
    ∃ b' : MvPolynomial (σ × Fin (n + 1)) A,
      (relativeFreeDeltaStructure σ D).delta
        (MvPolynomial.C c * MvPolynomial.X (s, n) +
          relativeFreeFiniteInitialPolynomialMap n σ A b) =
        MvPolynomial.C (D.frobeniusLift c) * MvPolynomial.X (s, n + 1) +
          relativeFreeFiniteInitialPolynomialMap (n + 1) σ A b' := by
  let i := relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
  let b₀ := MvPolynomial.rename (fun z : σ × Fin n => (z.1, z.2.castSucc)) b
  let x : MvPolynomial (σ × Fin (n + 1)) A := MvPolynomial.X (s, Fin.last n)
  have hb₀ : i b₀ = relativeFreeFiniteInitialPolynomialMap n σ A b := by
    simp only [i, b₀, relativeFreeFiniteInitialPolynomialMap, MvPolynomial.rename_rename,
      Function.comp_def, Fin.val_castSucc]
  have hx : i x = MvPolynomial.X (s, n) := by
    simp [i, x, relativeFreeFiniteInitialPolynomialMap]
  obtain ⟨g, hg⟩ := initial_delta_exists D n b
  let carry := (WittVector.teichmuller p (MvPolynomial.C c * x) +
    WittVector.teichmuller p b₀).coeff 1
  have hc : i carry = (WittVector.teichmuller p
      (MvPolynomial.C c * MvPolynomial.X (s, n)) +
      WittVector.teichmuller p (relativeFreeFiniteInitialPolynomialMap n σ A b)).coeff 1 := by
    change (WittVector.map i.toRingHom
      (WittVector.teichmuller p (MvPolynomial.C c * x) +
        WittVector.teichmuller p b₀)).coeff 1 = _
    rw [map_add, WittVector.map_teichmuller, WittVector.map_teichmuller]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, hx, hb₀]
    simp only [i, relativeFreeFiniteInitialPolynomialMap, MvPolynomial.rename_C]
  refine ⟨MvPolynomial.C (D.delta c) * x ^ p + g + carry, ?_⟩
  rw [DeltaStructure.delta_add, DeltaStructure.delta_mul,
    relativeFreeDeltaStructure_delta_C, relativeFreeDeltaStructure_delta_X, hg]
  change _ = _ + i (MvPolynomial.C (D.delta c) * x ^ p + g + carry)
  simp only [map_add, map_mul, map_pow, hx, hc]
  simp only [i, relativeFreeFiniteInitialPolynomialMap, MvPolynomial.rename_C]
  rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, map_natCast]
  ring

/-- 実関係式の第n変数は一次で係数φ^n(d)。残余は厳密に初期n段に属する。 -/
theorem exists_deltaDivisionFiniteLeadingLowerPolynomial
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    ∃ b : MvPolynomial (σ × Fin n) A,
      deltaDivisionIteratedRelation D d a s n =
        MvPolynomial.C (D.frobeniusLift^[n] d) * MvPolynomial.X (s, n) +
          relativeFreeFiniteInitialPolynomialMap n σ A b := by
  induction n with
  | zero =>
      refine ⟨-MvPolynomial.C (a s), ?_⟩
      simp [deltaDivisionIteratedRelation, relativeFreeFiniteInitialPolynomialMap, sub_eq_add_neg]
  | succ n ih =>
      obtain ⟨b, hb⟩ := ih
      obtain ⟨b', hb'⟩ := affine_delta_exists D (D.frobeniusLift^[n] d) s n b
      refine ⟨b', ?_⟩
      change (relativeFreeDeltaStructure σ D).delta^[n + 1] _ = _
      rw [Function.iterate_succ_apply']
      change (relativeFreeDeltaStructure σ D).delta
        (deltaDivisionIteratedRelation D d a s n) = _
      rw [hb, hb', Function.iterate_succ_apply']

/-- 最高変数を除いた、厳密に初期n段上の下位多項式。 -/
def deltaDivisionFiniteLeadingLowerPolynomial
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    MvPolynomial (σ × Fin n) A :=
  Classical.choose (exists_deltaDivisionFiniteLeadingLowerPolynomial D d a s n)

/-- 選んだ下位多項式による整係数の最高変数分離の等式。 -/
theorem deltaDivisionIteratedRelation_eq_leading_add_lower
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    deltaDivisionIteratedRelation D d a s n =
      MvPolynomial.C (D.frobeniusLift^[n] d) * MvPolynomial.X (s, n) +
        relativeFreeFiniteInitialPolynomialMap n σ A
          (deltaDivisionFiniteLeadingLowerPolynomial D d a s n) :=
  Classical.choose_spec (exists_deltaDivisionFiniteLeadingLowerPolynomial D d a s n)

/-- 下位多項式は厳密な初期段の単射性によって一意。 -/
theorem deltaDivisionFiniteLeadingLowerPolynomial_unique
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ)
    (b : MvPolynomial (σ × Fin n) A)
    (hb : deltaDivisionIteratedRelation D d a s n =
      MvPolynomial.C (D.frobeniusLift^[n] d) * MvPolynomial.X (s, n) +
        relativeFreeFiniteInitialPolynomialMap n σ A b) :
    b = deltaDivisionFiniteLeadingLowerPolynomial D d a s n := by
  apply relativeFreeFiniteInitialPolynomialMap_injective n σ
  exact add_left_cancel (hb.symm.trans
    (deltaDivisionIteratedRelation_eq_leading_add_lower D d a s n))

/-- 有限関係式自体にも整係数の一次分離が成り立つ。 -/
theorem deltaDivisionFiniteRelationPolynomial_eq_leading_add_lower
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ) (n : ℕ) :
    deltaDivisionFiniteRelationPolynomial D d a s n =
      MvPolynomial.C (D.frobeniusLift^[n] d) * MvPolynomial.X (s, Fin.last n) +
        MvPolynomial.rename (fun z : σ × Fin n => (z.1, z.2.castSucc))
          (deltaDivisionFiniteLeadingLowerPolynomial D d a s n) := by
  apply relativeFreeFiniteInitialPolynomialMap_injective (n + 1) σ
  rw [deltaDivisionFiniteRelationPolynomial_image,
    deltaDivisionIteratedRelation_eq_leading_add_lower]
  simp only [map_add, map_mul, relativeFreeFiniteInitialPolynomialMap,
    MvPolynomial.rename_C, MvPolynomial.rename_X, MvPolynomial.rename_rename,
    Function.comp_def, Fin.val_castSucc, Fin.val_last]

/-- p除算の実関係式の最高係数は全深さでp。 -/
theorem deltaPDivisionIteratedRelation_eq_leading_add_lower
    (D : DeltaStructure p A) (a : σ → A) (s : σ) (n : ℕ) :
    deltaDivisionIteratedRelation D (p : A) a s n =
      (p : RelativeFreeDeltaRing (R := A) σ) * MvPolynomial.X (s, n) +
        relativeFreeFiniteInitialPolynomialMap n σ A
          (deltaDivisionFiniteLeadingLowerPolynomial D (p : A) a s n) := by
  have hp : D.frobeniusLift^[n] (p : A) = p := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_natCast]
  rw [deltaDivisionIteratedRelation_eq_leading_add_lower, hp, map_natCast]

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteLeadingLinear

/-! ## 全反復除算関係式の最高偏微分のp剰余像

任意深さの最高偏微分を、基底Frobeniusの反復で表す。
-/

@[expose] public noncomputable section DeltaDivisionFiniteTopDerivative

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type w} [CommRing B] {σ : Type v}
attribute [local instance] Classical.propDecidable

/-- 任意深さの除算関係式の最高偏微分は、通常p剰余でφ^n(d)となる。
対応しない生成元の最高偏微分は零。 -/
theorem deltaDivisionFiniteRelationPolynomial_top_derivative
    (D : DeltaStructure p A) (d : A) (a : σ → A) (t : σ) (n : ℕ)
    (q : MvPolynomial (σ × Fin (n + 1)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (n + 1)) A) = 0) (s : σ) :
    q (MvPolynomial.pderiv (s, Fin.last n) (deltaDivisionFiniteRelationPolynomial D d a t n)) =
      if s = t then q (MvPolynomial.C (D.frobeniusLift^[n] d)) else 0 := by
  classical
  induction n with
  | zero =>
      by_cases h : s = t
      · subst t
        simp [deltaDivisionFiniteRelationPolynomial, MvPolynomial.pderiv_X]
      · simp [deltaDivisionFiniteRelationPolynomial, MvPolynomial.pderiv_X, h]
  | succ n ih =>
      rw [deltaDivisionFiniteRelationPolynomial_succ,
        relativeFreeFiniteDeltaTopDerivative_eq_frobenius_pderiv n σ D q hp]
      let q₀ := q.comp (relativeFreeFiniteFrobeniusStep n σ D)
      have hp₀ : q₀ (p : MvPolynomial (σ × Fin (n + 1)) A) = 0 := by
        simpa only [q₀, RingHom.comp_apply, map_natCast] using hp
      have he := ih q₀ hp₀
      change q₀ (MvPolynomial.pderiv (s, Fin.last n)
        (deltaDivisionFiniteRelationPolynomial D d a t n)) = _
      rw [he]
      split_ifs with h
      · change q (relativeFreeFiniteFrobeniusStep n σ D
          (MvPolynomial.C (D.frobeniusLift^[n] d))) = _
        rw [relativeFreeFiniteFrobeniusStep_C, Function.iterate_succ_apply']
      · rfl

/-- 対応する生成元の最高偏微分はφ^n(d)の係数像。 -/
theorem deltaDivisionFiniteRelationPolynomial_top_derivative_self
    (D : DeltaStructure p A) (d : A) (a : σ → A) (t : σ) (n : ℕ)
    (q : MvPolynomial (σ × Fin (n + 1)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (n + 1)) A) = 0) :
    q (MvPolynomial.pderiv (t, Fin.last n) (deltaDivisionFiniteRelationPolynomial D d a t n)) =
      q (MvPolynomial.C (D.frobeniusLift^[n] d)) := by
  simpa using deltaDivisionFiniteRelationPolynomial_top_derivative D d a t n q hp t

/-- 別の生成元の最高偏微分は零。 -/
theorem deltaDivisionFiniteRelationPolynomial_top_derivative_of_ne
    (D : DeltaStructure p A) (d : A) (a : σ → A) (t : σ) (n : ℕ)
    (q : MvPolynomial (σ × Fin (n + 1)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (n + 1)) A) = 0) (s : σ) (hs : s ≠ t) :
    q (MvPolynomial.pderiv (s, Fin.last n)
      (deltaDivisionFiniteRelationPolynomial D d a t n)) = 0 := by
  simpa only [ite_eq_right hs] using
    deltaDivisionFiniteRelationPolynomial_top_derivative D d a t n q hp s

/-- p,dを消す通常射では全反復関係式の最高偏微分の像は零。 -/
theorem deltaDivisionFiniteRelationPolynomial_top_derivative_of_prime_generator_zero
    (D : DeltaStructure p A) (d : A) (a : σ → A) (t : σ) (n : ℕ)
    (q : MvPolynomial (σ × Fin (n + 1)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (n + 1)) A) = 0)
    (hd : q (MvPolynomial.C d) = 0) (s : σ) :
    q (MvPolynomial.pderiv (s, Fin.last n)
      (deltaDivisionFiniteRelationPolynomial D d a t n)) = 0 := by
  let f := q.comp (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (n + 1)) A)
  have hp' : f (p : A) = 0 := by
    simpa only [f, RingHom.comp_apply, map_natCast] using hp
  have hz (m : ℕ) : f (D.frobeniusLift^[m] d) = 0 := by
    induction m with
    | zero => exact hd
    | succ m ih =>
        rw [Function.iterate_succ_apply', D.frobeniusLift_apply, map_add, map_pow, map_mul,
          hp', ih, zero_mul, add_zero, zero_pow (Fact.out : p.Prime).ne_zero]
  rw [deltaDivisionFiniteRelationPolynomial_top_derivative D d a t n q hp s]
  split_ifs
  · exact hz n
  · rfl

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteTopDerivative

/-! ## 全反復除算関係式の最高変数係数と次数

通常p剰余で各深さの最高係数を基底Frobeniusの反復で表す。
-/

@[expose] public noncomputable section DeltaDivisionFiniteTopCoefficient

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
attribute [local instance] Classical.propDecidable

/-- 深さn+1の実際の関係式を最高変数分離・係数p商で表した多項式。 -/
def deltaDivisionFiniteTopResidue (D : DeltaStructure p A) (d : A) (a : σ → A) (t : σ) (n : ℕ) :
    MvPolynomial σ (RelativeFreeFiniteOldResidue (p := p) (A := A) n σ) :=
  relativeFreeFiniteTopResidueMap (p := p) n σ
    (deltaDivisionFiniteRelationPolynomial D d a t (n + 1))

/-- 基底Frobeniusの次の反復のp商像は、前の反復像のp乗。 -/
theorem deltaDivisionFiniteOldResidue_frobenius_iterate (D : DeltaStructure p A) (d : A) (n : ℕ) :
    (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (n + 1)) A)})
      (MvPolynomial.C (D.frobeniusLift^[n] d))) ^ p =
    Ideal.Quotient.mk _ (MvPolynomial.C (D.frobeniusLift^[n + 1] d)) := by
  let q := Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (n + 1)) A)})
  let f := q.comp (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (n + 1)) A)
  have hp : q (p : MvPolynomial (σ × Fin (n + 1)) A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hp' : f (p : A) = 0 := by simpa only [f, RingHom.comp_apply, map_natCast] using hp
  change (f (D.frobeniusLift^[n] d)) ^ p = f (D.frobeniusLift^[n + 1] d)
  rw [Function.iterate_succ_apply', D.frobeniusLift_apply, map_add, map_pow, map_mul,
    hp', zero_mul, add_zero]

/-- 全深さの最高変数係数はφ^(n+1)(d)の係数像、別の生成元では零。 -/
theorem deltaDivisionFiniteTopResidue_coefficient (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) (s : σ) :
    (deltaDivisionFiniteTopResidue D d a t n).coeff (Finsupp.single s 1) =
      if s = t then Ideal.Quotient.mk _ (MvPolynomial.C (D.frobeniusLift^[n + 1] d)) else 0 := by
  unfold deltaDivisionFiniteTopResidue
  rw [deltaDivisionFiniteRelationPolynomial_succ,
    relativeFreeFiniteDeltaTopCoefficient_eq_pderiv_pow]
  have hp : Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (n + 1)) A)})
      (p : MvPolynomial (σ × Fin (n + 1)) A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [deltaDivisionFiniteRelationPolynomial_top_derivative D d a t n _ hp s]
  split_ifs with h
  · exact deltaDivisionFiniteOldResidue_frobenius_iterate (σ := σ) D d n
  · rw [zero_pow (Fact.out : p.Prime).ne_zero]

/-- 自己生成元の最高変数係数の公開版。 -/
theorem deltaDivisionFiniteTopResidue_coefficient_self (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) :
    (deltaDivisionFiniteTopResidue D d a t n).coeff (Finsupp.single t 1) =
      Ideal.Quotient.mk _ (MvPolynomial.C (D.frobeniusLift^[n + 1] d)) := by
  simpa using deltaDivisionFiniteTopResidue_coefficient D d a t n t

/-- 別の生成元の最高変数係数は零。 -/
theorem deltaDivisionFiniteTopResidue_coefficient_of_ne (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) (s : σ) (h : s ≠ t) :
    (deltaDivisionFiniteTopResidue D d a t n).coeff (Finsupp.single s 1) = 0 := by
  simpa only [ite_eq_right h] using deltaDivisionFiniteTopResidue_coefficient D d a t n s

/-- 全反復関係式の最高変数全体に関する次数はp剰余で1以下。 -/
theorem deltaDivisionFiniteTopResidue_degree_le_one (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) :
    (deltaDivisionFiniteTopResidue D d a t n).totalDegree ≤ 1 := by
  unfold deltaDivisionFiniteTopResidue
  rw [deltaDivisionFiniteRelationPolynomial_succ]
  exact relativeFreeFiniteDeltaStep_top_degree n σ D _

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteTopCoefficient

/-! ## 係数の(p,d)剰余での全反復関係式の最高係数消滅

p商の係数をさらにdで割る。係数商にδ構造は要求しない。
-/

@[expose] public noncomputable section DeltaDivisionFiniteGeneratorResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 初期p係数商をさらにdの標準係数像で割った環。 -/
abbrev DeltaDivisionFiniteGeneratorCoefficient (d : A) (n : ℕ) :=
  RelativeFreeFiniteOldResidue (p := p) (A := A) n σ ⧸
    Ideal.span {(Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (n + 1)) A)})
      (MvPolynomial.C d))}

/-- 深さn+1の最高変数表示を、係数の(p,d)商へ送った多項式。 -/
def deltaDivisionFiniteGeneratorResidue (D : DeltaStructure p A) (d : A)
    (a : σ → A) (t : σ) (n : ℕ) :
    MvPolynomial σ (DeltaDivisionFiniteGeneratorCoefficient (p := p) (σ := σ) d n) :=
  MvPolynomial.map (Ideal.Quotient.mk _ : RelativeFreeFiniteOldResidue (p := p) (A := A) n σ →+*
    DeltaDivisionFiniteGeneratorCoefficient (p := p) (σ := σ) d n)
    (deltaDivisionFiniteTopResidue D d a t n)

/-- この係数商では、基底Frobeniusの全反復のd像は零。 -/
theorem deltaDivisionFiniteGeneratorCoefficient_frobenius_zero (D : DeltaStructure p A)
    (d : A) (n m : ℕ) :
    (Ideal.Quotient.mk _ : RelativeFreeFiniteOldResidue (p := p) (A := A) n σ →+*
      DeltaDivisionFiniteGeneratorCoefficient (p := p) (σ := σ) d n)
      (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (n + 1)) A)})
        (MvPolynomial.C (D.frobeniusLift^[m] d))) = 0 := by
  let q := Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (n + 1)) A)})
  let r : RelativeFreeFiniteOldResidue (p := p) (A := A) n σ →+*
      DeltaDivisionFiniteGeneratorCoefficient (p := p) (σ := σ) d n := Ideal.Quotient.mk _
  let f := r.comp (q.comp (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (n + 1)) A))
  have hp₀ : q (p : MvPolynomial (σ × Fin (n + 1)) A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hp : f (p : A) = 0 := by
    change r (q (MvPolynomial.C (p : A))) = 0
    rw [map_natCast (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (n + 1)) A), hp₀, map_zero]
  have hd : f d = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  change f (D.frobeniusLift^[m] d) = 0
  induction m with
  | zero => exact hd
  | succ m ih =>
      rw [Function.iterate_succ_apply', D.frobeniusLift_apply, map_add, map_pow, map_mul,
        hp, ih, zero_mul, add_zero, zero_pow (Fact.out : p.Prime).ne_zero]

/-- 係数の(p,d)商で全最高変数係数は零。 -/
theorem deltaDivisionFiniteGeneratorResidue_coefficient_zero (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) (s : σ) :
    (deltaDivisionFiniteGeneratorResidue D d a t n).coeff (Finsupp.single s 1) = 0 := by
  classical
  rw [deltaDivisionFiniteGeneratorResidue, MvPolynomial.coeff_map,
    deltaDivisionFiniteTopResidue_coefficient]
  split_ifs
  · exact deltaDivisionFiniteGeneratorCoefficient_frobenius_zero (σ := σ) D d n (n + 1)
  · exact map_zero _

/-- 係数のd商への写像でも最高変数次数の1以下という上界を保つ。 -/
theorem deltaDivisionFiniteGeneratorResidue_degree_le_one (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) :
    (deltaDivisionFiniteGeneratorResidue D d a t n).totalDegree ≤ 1 := by
  have he : (deltaDivisionFiniteGeneratorResidue D d a t n).totalDegree ≤
      (deltaDivisionFiniteTopResidue D d a t n).totalDegree := by
    unfold deltaDivisionFiniteGeneratorResidue MvPolynomial.totalDegree
    exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  exact he.trans (deltaDivisionFiniteTopResidue_degree_le_one D d a t n)

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteGeneratorResidue

/-! ## 全反復関係式の(p,d)係数商での最高変数除去

次数1以下と全一次係数の消滅から、最高変数分離表示の定数性を導く。
-/

@[expose] public noncomputable section DeltaDivisionFiniteGeneratorConstant

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

private theorem constant_of_linear_coefficients_zero {R : Type*} [CommRing R]
    (f : MvPolynomial σ R) (hdeg : f.totalDegree ≤ 1)
    (hcoeff : ∀ s, f.coeff (Finsupp.single s 1) = 0) :
    f = MvPolynomial.C (f.coeff 0) := by
  classical
  ext m
  rw [MvPolynomial.coeff_C]
  split_ifs with hm
  · rw [← hm]
  · by_contra hc
    have hs : m ∈ f.support := MvPolynomial.mem_support_iff.mpr hc
    have hd : m.degree ≤ 1 := (MvPolynomial.le_totalDegree hs).trans hdeg
    have hpos : 0 < m.degree := Nat.pos_of_ne_zero (fun hz =>
      hm ((Finsupp.degree_eq_zero_iff m).mp hz).symm)
    have hone : m.sum (fun _ k => k) = 1 := by
      change m.degree = 1
      omega
    obtain ⟨s, rfl⟩ := (Finsupp.sum_eq_one_iff _).mp hone
    exact hc (hcoeff s)

/-- 全深さで、係数の(p,d)商に送ると新しい最高変数への依存は消える。 -/
theorem deltaDivisionFiniteGeneratorResidue_eq_C (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) :
    deltaDivisionFiniteGeneratorResidue D d a t n =
      MvPolynomial.C ((deltaDivisionFiniteGeneratorResidue D d a t n).coeff 0) := by
  exact constant_of_linear_coefficients_zero _
    (deltaDivisionFiniteGeneratorResidue_degree_le_one D d a t n)
    (deltaDivisionFiniteGeneratorResidue_coefficient_zero D d a t n)

/-- 全深さの最高変数剰余多項式の全体次数は零。 -/
theorem deltaDivisionFiniteGeneratorResidue_totalDegree_zero (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) :
    (deltaDivisionFiniteGeneratorResidue D d a t n).totalDegree = 0 := by
  exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mpr
    (deltaDivisionFiniteGeneratorResidue_eq_C D d a t n)

/-- 最高変数を零にした、初期有限変数だけの具体的な関係式。 -/
def deltaDivisionFiniteLowerRelation (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) : MvPolynomial (σ × Fin (n + 1)) A :=
  MvPolynomial.constantCoeff
    (relativeFreeFiniteTopVariableSplitAlgEquiv n σ A
      (deltaDivisionFiniteRelationPolynomial D d a t (n + 1)))

/-- 全深さの関係式は(p,d)係数商で、最高変数を零にした初期多項式の像に一致する。 -/
theorem deltaDivisionFiniteGeneratorResidue_eq_lowerRelation (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) :
    deltaDivisionFiniteGeneratorResidue D d a t n =
      MvPolynomial.C
        ((Ideal.Quotient.mk _ : RelativeFreeFiniteOldResidue (p := p) (A := A) n σ →+*
          DeltaDivisionFiniteGeneratorCoefficient (p := p) (σ := σ) d n)
          (Ideal.Quotient.mk _ (deltaDivisionFiniteLowerRelation D d a t n))) := by
  rw [deltaDivisionFiniteGeneratorResidue_eq_C]
  congr 1

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteGeneratorConstant
