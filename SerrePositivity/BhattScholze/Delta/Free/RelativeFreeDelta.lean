module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.Algebra.MvPolynomial.CommRing
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import Mathlib.Logic.Function.Iterate
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaQuotient
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# 多項式環上の δ 構造と相対自由 δ 環（BS 著者版 Notation 2.8、BS 著者版 Lemma 2.11、BS 著者版 Example 2.10）

## 概要
多項式環に係数の δ と変数の δ の値を指定した δ 構造（変数を rank 1 にする補助構造を含む）、
基底 δ 環 R 上の相対自由 δ 環 R{x_s} = R[x_(s,n)] とその普遍性、生成元と関係式による表示、変数の分割。
BS 著者版 Notation 2.8・Lemma 2.11 の相対版。

## 方針
W₂ 切断を多項式環の普遍性で直接与える。p ねじれなしの議論を使わない。

## 規約
基底・終域の p ねじれを許す。

## 使われ方
元の添加と表示のすべて（d で割る包 Division、André、DividedPower）。
-/

@[expose] public noncomputable section
universe u v w

/-! ## 変数のδ値を指定した多項式δ構造

基底のW₂切断を係数に用い、変数を指定された二つのWitt座標へ送る。
また、任意の多項式δ構造からの環射がδ射であることを係数と変数上で判定する。
-/

section PolynomialDelta

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] (σ : Type v)

/-- 係数のδ切断を延長し、各変数のδ値を指定するW₂切断。 -/
def polynomialDeltaSection (D : DeltaStructure p R) (v : σ → MvPolynomial σ R) :
    MvPolynomial σ R →+* WittTwo p (MvPolynomial σ R) :=
  MvPolynomial.eval₂Hom ((wittTwoMap (p := p) MvPolynomial.C).comp D.sectionHom)
    (fun s ↦ TruncatedWittVector.mk p (fun i ↦ if i = 0 then MvPolynomial.X s else v s))

/-- 多項式切断は係数上で元の切断をW₂係数写像で移したもの。 -/
@[simp] theorem polynomialDeltaSection_C (D : DeltaStructure p R)
    (v : σ → MvPolynomial σ R) (r : R) :
    polynomialDeltaSection σ D v (MvPolynomial.C r) =
      wittTwoMap MvPolynomial.C (D.sectionHom r) :=
  MvPolynomial.eval₂Hom_C _ _ r

/-- 多項式切断の変数上のW₂座標。有限段との自然性でもこの式を使う。 -/
@[simp] theorem polynomialDeltaSection_X (D : DeltaStructure p R)
    (v : σ → MvPolynomial σ R) (s : σ) :
    polynomialDeltaSection σ D v (MvPolynomial.X s) =
      TruncatedWittVector.mk p (fun i ↦ if i = 0 then MvPolynomial.X s else v s) :=
  MvPolynomial.eval₂Hom_X' _ _ s

/-- 指定した変数δ値によらず、W₂切断の第0座標は恒等射。 -/
theorem polynomialDeltaSection_projection (D : DeltaStructure p R)
    (v : σ → MvPolynomial σ R) :
    (wittTwoProjection p (MvPolynomial σ R)).comp (polynomialDeltaSection σ D v) =
      RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, polynomialDeltaSection, MvPolynomial.eval₂Hom_C,
      wittTwoProjection_apply, wittTwoMap_coeff]
    rw [D.coeff_zero]
    rfl
  · intro s
    simp [polynomialDeltaSection]

/-- 係数のδ構造と各変数のδ値から得られる多項式δ構造。 -/
def polynomialDeltaStructure (D : DeltaStructure p R) (v : σ → MvPolynomial σ R) :
    DeltaStructure p (MvPolynomial σ R) where
  sectionHom := polynomialDeltaSection σ D v
  coeff_zero := by
    intro f
    exact RingHom.congr_fun (polynomialDeltaSection_projection σ D v) f

/-- 多項式δ構造は係数上で元のδ構造に一致する。 -/
@[simp] theorem polynomialDeltaStructure_delta_C (D : DeltaStructure p R)
    (v : σ → MvPolynomial σ R) (r : R) :
    (polynomialDeltaStructure σ D v).delta (MvPolynomial.C r) =
      MvPolynomial.C (D.delta r) := by
  simp [DeltaStructure.delta, polynomialDeltaStructure, polynomialDeltaSection]

/-- 多項式δ構造は各変数上で指定したδ値を持つ。 -/
@[simp] theorem polynomialDeltaStructure_delta_X (D : DeltaStructure p R)
    (v : σ → MvPolynomial σ R) (s : σ) :
    (polynomialDeltaStructure σ D v).delta (MvPolynomial.X s) = v s := by
  simp [DeltaStructure.delta, polynomialDeltaStructure, polynomialDeltaSection]

/-- 多項式δ構造への係数射はδ射。 -/
theorem polynomialDeltaStructure_C_isDeltaHom (D : DeltaStructure p R)
    (v : σ → MvPolynomial σ R) :
    D.IsDeltaHom (polynomialDeltaStructure σ D v) MvPolynomial.C := by
  intro r
  exact (polynomialDeltaStructure_delta_C σ D v r).symm

namespace DeltaStructure
variable {σ} {A : Type w} [CommRing A]

/-- 係数上のW₂切断の自然性と変数上のδ両立性から、多項式環上のδ射を判定する。
整数係数では係数側の条件は環準同型の一意性だけで従う。 -/
theorem isDeltaHom_mvPolynomial_of_sectionHom_comp_C
    (D : DeltaStructure p (MvPolynomial σ R)) (E : DeltaStructure p A)
    (f : MvPolynomial σ R →+* A)
    (hC : ((wittTwoMap (p := p) f).comp D.sectionHom).comp MvPolynomial.C =
      (E.sectionHom.comp f).comp MvPolynomial.C)
    (hX : ∀ s, f (D.delta (MvPolynomial.X s)) = E.delta (f (MvPolynomial.X s))) :
    D.IsDeltaHom E f := by
  apply (D.isDeltaHom_iff_sectionHom_comp E f).mpr
  apply MvPolynomial.ringHom_ext' hC
  intro s
  apply TruncatedWittVector.ext
  intro i
  fin_cases i
  · simp only [RingHom.comp_apply, wittTwoMap_coeff]
    change f ((D.sectionHom (MvPolynomial.X s)).coeff 0) =
      (E.sectionHom (f (MvPolynomial.X s))).coeff 0
    rw [D.coeff_zero, E.coeff_zero]
  · simp only [RingHom.comp_apply, wittTwoMap_coeff]
    exact hX s

/-- 任意の多項式δ構造からの環射は、係数と変数上でδと可換ならδ射。
p正則性や非零性を要求せず、W₂切断の二座標を比較する。 -/
theorem isDeltaHom_mvPolynomial (D : DeltaStructure p (MvPolynomial σ R))
    (E : DeltaStructure p A) (f : MvPolynomial σ R →+* A)
    (hC : ∀ r, f (D.delta (MvPolynomial.C r)) = E.delta (f (MvPolynomial.C r)))
    (hX : ∀ s, f (D.delta (MvPolynomial.X s)) = E.delta (f (MvPolynomial.X s))) :
    D.IsDeltaHom E f := by
  apply D.isDeltaHom_mvPolynomial_of_sectionHom_comp_C E f _ hX
  apply RingHom.ext
  intro r
  apply TruncatedWittVector.ext
  intro i
  fin_cases i
  · simp only [RingHom.comp_apply, wittTwoMap_coeff]
    change f ((D.sectionHom (MvPolynomial.C r)).coeff 0) =
      (E.sectionHom (f (MvPolynomial.C r))).coeff 0
    rw [D.coeff_zero, E.coeff_zero]
  · simp only [RingHom.comp_apply, wittTwoMap_coeff]
    exact hC r

end DeltaStructure
end SerrePositivity.BhattScholze

end PolynomialDelta

/-! ## rank 1変数を持つ補助多項式δ構造

基底δ構造を係数に延長し、各変数のδを零とする。
相対自由δ環の次座標へ移るδ構造とは区別する。
-/

section PolynomialRankOneDelta

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (σ : Type v)

/-- 係数のδ切断と、rank 1変数のW₂座標による多項式切断。 -/
def polynomialRankOneDeltaSection (D : DeltaStructure p A) :
    MvPolynomial σ A →+* WittTwo p (MvPolynomial σ A) :=
  polynomialDeltaSection σ D (fun _ ↦ 0)

/-- 補助切断の第0座標は恒等射。 -/
theorem polynomialRankOneDeltaSection_projection (D : DeltaStructure p A) :
    (wittTwoProjection p (MvPolynomial σ A)).comp (polynomialRankOneDeltaSection σ D) =
      RingHom.id _ :=
  polynomialDeltaSection_projection σ D _

/-- 変数がrank 1である補助多項式δ構造。 -/
def polynomialRankOneDeltaStructure (D : DeltaStructure p A) :
    DeltaStructure p (MvPolynomial σ A) :=
  polynomialDeltaStructure σ D (fun _ ↦ 0)

/-- 補助δ構造は基底係数上で元のδ構造に一致する。 -/
@[simp] theorem polynomialRankOneDeltaStructure_delta_C (D : DeltaStructure p A) (a : A) :
    (polynomialRankOneDeltaStructure σ D).delta (MvPolynomial.C a) =
      MvPolynomial.C (D.delta a) := by
  exact polynomialDeltaStructure_delta_C σ D _ a

/-- 補助δ構造では各変数のδは零。 -/
@[simp] theorem polynomialRankOneDeltaStructure_delta_X (D : DeltaStructure p A) (s : σ) :
    (polynomialRankOneDeltaStructure σ D).delta (MvPolynomial.X s) = 0 := by
  exact polynomialDeltaStructure_delta_X σ D _ s

/-- 補助多項式δ構造への係数射はδ射。 -/
theorem polynomialRankOneDeltaStructure_C_isDeltaHom (D : DeltaStructure p A) :
    D.IsDeltaHom (polynomialRankOneDeltaStructure σ D) MvPolynomial.C :=
  polynomialDeltaStructure_C_isDeltaHom σ D _

/-- rank 1変数のFrobenius像はp乗。 -/
@[simp] theorem polynomialRankOneDeltaStructure_frobenius_X (D : DeltaStructure p A) (s : σ) :
    (polynomialRankOneDeltaStructure σ D).frobeniusLift (MvPolynomial.X s) =
      MvPolynomial.X s ^ p := by
  rw [DeltaStructure.frobeniusLift_apply, polynomialRankOneDeltaStructure_delta_X,
    mul_zero, add_zero]

/-- rank 1変数のp乗もrank 1。 -/
@[simp] theorem polynomialRankOneDeltaStructure_delta_X_pow_prime (D : DeltaStructure p A) (s : σ) :
    (polynomialRankOneDeltaStructure σ D).delta (MvPolynomial.X s ^ p) = 0 := by
  have h := (polynomialRankOneDeltaStructure σ D).p_mul_delta_dvd_delta_pow (MvPolynomial.X s)
  rw [polynomialRankOneDeltaStructure_delta_X, mul_zero, zero_dvd_iff] at h
  exact h

end SerrePositivity.BhattScholze

end PolynomialRankOneDelta

/-! ## 基底δ環上の相対自由δ環

基底のW₂切断を係数に用い、x_(s,n)を(x_(s,n),x_(s,n+1))へ送る切断を構成する。
pねじれを持つ基底にも適用できる、BS 著者版 Notation 2.8・BS 著者版 Lemma 2.11の相対構成。
-/

section RelativeFreeDelta

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] (σ : Type v)

/-- 相対自由δ環の台環（BS 著者版 Notation 2.8 の任意の族を添加する記法の実装）。
  変数x_(s,n)はδ^n(x_s)を表す。 -/
abbrev RelativeFreeDeltaRing := MvPolynomial (σ × ℕ) R

/-- 相対自由δ環の切断。係数には基底の切断を、変数には次のδ座標を用いる。 -/
def relativeFreeDeltaSection (D : DeltaStructure p R) :
    RelativeFreeDeltaRing (R := R) σ →+* WittTwo p (RelativeFreeDeltaRing (R := R) σ) :=
  polynomialDeltaSection (σ × ℕ) D (fun v ↦ MvPolynomial.X (v.1, v.2 + 1))

/-- 相対自由切断と第0座標射の合成は恒等写像。係数と変数上で確認する。 -/
theorem relativeFreeDeltaSection_projection (D : DeltaStructure p R) :
    (wittTwoProjection p (RelativeFreeDeltaRing (R := R) σ)).comp
      (relativeFreeDeltaSection σ D) = RingHom.id _ :=
  polynomialDeltaSection_projection (σ × ℕ) D _

/-- 相対自由δ構造。第0座標の切断条件を満たすW₂準同型から直接構成する。
基底のp正則性・非零性・完備性は要求しない。 -/
def relativeFreeDeltaStructure (D : DeltaStructure p R) :
    DeltaStructure p (RelativeFreeDeltaRing (R := R) σ) :=
  polynomialDeltaStructure (σ × ℕ) D (fun v ↦ MvPolynomial.X (v.1, v.2 + 1))

/-- 基底係数上のδは基底のδと一致する。 -/
@[simp] theorem relativeFreeDeltaStructure_delta_C (D : DeltaStructure p R) (r : R) :
    (relativeFreeDeltaStructure σ D).delta (MvPolynomial.C r) = MvPolynomial.C (D.delta r) := by
  exact polynomialDeltaStructure_delta_C (σ × ℕ) D _ r

/-- 相対自由δ環の生成元のδは次の座標。 -/
@[simp] theorem relativeFreeDeltaStructure_delta_X (D : DeltaStructure p R) (s : σ) (n : ℕ) :
    (relativeFreeDeltaStructure σ D).delta (MvPolynomial.X (s, n)) =
      MvPolynomial.X (s, n + 1) := by
  exact polynomialDeltaStructure_delta_X (σ × ℕ) D _ (s, n)

/-- 相対自由δ環への係数射はδ射。 -/
theorem relativeFreeDeltaStructure_C_isDeltaHom (D : DeltaStructure p R) :
    D.IsDeltaHom (relativeFreeDeltaStructure σ D) MvPolynomial.C :=
  polynomialDeltaStructure_C_isDeltaHom (σ × ℕ) D _

end SerrePositivity.BhattScholze

end RelativeFreeDelta

/-! ## 相対自由δ環の普遍性

任意の基底δ射と生成元像の指定から、基底と両立する一意なδ射を構成する。
基底・終域のpねじれを許す。BS 著者版 Notation 2.8のδ元の添加に用いる。
-/

section RelativeFreeUniversal

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
    {σ : Type v} {A : Type w} [CommRing A]

/-- 基底射fと元族a_sから、各x_(s,n)をδ^n(a_s)へ評価する環準同型。 -/
def relativeFreeDeltaEval (E : DeltaStructure p A) (f : R →+* A) (a : σ → A) :
    RelativeFreeDeltaRing (R := R) σ →+* A :=
  MvPolynomial.eval₂Hom f (fun v ↦ E.delta^[v.2] (a v.1))

/-- 相対評価射は係数上で基底射fに一致する。 -/
@[simp] theorem relativeFreeDeltaEval_C (E : DeltaStructure p A) (f : R →+* A)
    (a : σ → A) (r : R) : relativeFreeDeltaEval E f a (MvPolynomial.C r) = f r := by
  simp [relativeFreeDeltaEval]

/-- 相対評価射の生成元上の値。 -/
@[simp] theorem relativeFreeDeltaEval_X (E : DeltaStructure p A) (f : R →+* A)
    (a : σ → A) (s : σ) (n : ℕ) :
    relativeFreeDeltaEval E f a (MvPolynomial.X (s, n)) = E.delta^[n] (a s) := by
  simp [relativeFreeDeltaEval]

/-- 基底射がδ射なら相対評価射もδ射。W₂切断の自然性を係数・変数の二座標で確認する。 -/
theorem relativeFreeDeltaEval_isDeltaHom (D : DeltaStructure p R) (E : DeltaStructure p A)
    (f : R →+* A) (hf : D.IsDeltaHom E f) (a : σ → A) :
    (relativeFreeDeltaStructure σ D).IsDeltaHom E (relativeFreeDeltaEval E f a) := by
  apply DeltaStructure.isDeltaHom_mvPolynomial
  · intro r
    rw [relativeFreeDeltaStructure_delta_C, relativeFreeDeltaEval_C,
      relativeFreeDeltaEval_C, hf r]
  · rintro ⟨s, n⟩
    rw [relativeFreeDeltaStructure_delta_X, relativeFreeDeltaEval_X,
      relativeFreeDeltaEval_X, Function.iterate_succ_apply']

/-- 相対自由δ環からのδ射では、全座標の像が初期座標の像から決まる。 -/
theorem relativeFreeDeltaHom_X_iterates (D : DeltaStructure p R) (E : DeltaStructure p A)
    (g : RelativeFreeDeltaRing (R := R) σ →+* A)
    (hg : (relativeFreeDeltaStructure σ D).IsDeltaHom E g) (s : σ) (n : ℕ) :
    g (MvPolynomial.X (s, n)) = E.delta^[n] (g (MvPolynomial.X (s, 0))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [← relativeFreeDeltaStructure_delta_X σ D s n, hg, ih, Function.iterate_succ_apply']

/-- 任意の基底δ射f:R→Aと元族a_sに対し、基底上f、初期生成元上a_sとなるδ射が一意に存在（BS 著者版 Notation 2.8 の添加の普遍性）。
基底射との両立条件を具体的な環準同型の等式で述べ、完備性・p正則性を要求しない。 -/
theorem existsUnique_relativeFreeDeltaHom (D : DeltaStructure p R) (E : DeltaStructure p A)
    (f : R →+* A) (hf : D.IsDeltaHom E f) (a : σ → A) :
    ∃! g : RelativeFreeDeltaRing (R := R) σ →+* A,
      (relativeFreeDeltaStructure σ D).IsDeltaHom E g ∧
        g.comp MvPolynomial.C = f ∧ ∀ s : σ, g (MvPolynomial.X (s, 0)) = a s := by
  have hC : (relativeFreeDeltaEval E f a).comp MvPolynomial.C = f := by
    ext r
    simp
  refine ⟨relativeFreeDeltaEval E f a,
    ⟨relativeFreeDeltaEval_isDeltaHom D E f hf a, hC, ?_⟩, ?_⟩
  · intro s
    simp
  · intro g hg
    apply MvPolynomial.ringHom_ext' (hg.2.1.trans hC.symm)
    rintro ⟨s, n⟩
    rw [relativeFreeDeltaHom_X_iterates D E g hg.1 s n, hg.2.2 s, relativeFreeDeltaEval_X]

end SerrePositivity.BhattScholze

end RelativeFreeUniversal

/-! ## 基底δ環上の生成元と関係式

相対自由δ環のイデアルのδ閉包で割り、指定した関係式と基底δ射を満たす
普遍δ射を構成する。BS 著者版 Notation 2.8・BS 著者版 Example 2.10の相対構成。
-/

section RelativeFreePresentation

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
    {σ : Type v} {A : Type w} [CommRing A]

/-- 基底δ射fと元族a_sへの評価がIを零に送れば、相対自由δ環のδ閉包商から
基底上f、初期生成元上a_sとなるδ射が一意に存在する（BS 著者版 Notation 2.8 の添加と関係式の δ 商の普遍性）。
具体的な商・商δ構造・基底の標準射との両立を公開型に含める。 -/
theorem existsUnique_relativeFreePresentationHom (D : DeltaStructure p R)
    (E : DeltaStructure p A) (f : R →+* A) (hf : D.IsDeltaHom E f) (a : σ → A)
    (I : Ideal (RelativeFreeDeltaRing (R := R) σ))
    (hI : ∀ r ∈ I, relativeFreeDeltaEval E f a r = 0) :
    ∃! g : (RelativeFreeDeltaRing (R := R) σ ⧸
        (relativeFreeDeltaStructure σ D).deltaClosure I) →+* A,
      ((relativeFreeDeltaStructure σ D).quotient
        ((relativeFreeDeltaStructure σ D).deltaClosure I)
        ((relativeFreeDeltaStructure σ D).isStable_deltaClosure I)).IsDeltaHom E g ∧
      g.comp ((Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure I)).comp
        MvPolynomial.C) = f ∧
      ∀ s : σ, g (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure I)
        (MvPolynomial.X (s, 0))) = a s := by
  let F := relativeFreeDeltaStructure σ D
  let J := F.deltaClosure I
  let q := Ideal.Quotient.mk J
  let t := relativeFreeDeltaEval E f a
  have ht : F.IsDeltaHom E t := relativeFreeDeltaEval_isDeltaHom D E f hf a
  have htC : t.comp MvPolynomial.C = f := by
    ext r
    simp [t]
  have htgen : ∀ s : σ, t (MvPolynomial.X (s, 0)) = a s := by
    intro s
    simp [t]
  have hker : I ≤ RingHom.ker t := fun r hr ↦ hI r hr
  obtain ⟨g, hg, hgu⟩ := F.existsUnique_deltaClosure_quotient_lift I E t ht hker
  refine ⟨g, ⟨hg.2, ?_, ?_⟩, ?_⟩
  · change g.comp (q.comp MvPolynomial.C) = f
    rw [← RingHom.comp_assoc, hg.1, htC]
  · intro s
    exact (DFunLike.congr_fun hg.1 (MvPolynomial.X (s, 0))).trans (htgen s)
  · intro k hk
    have hkδ : F.IsDeltaHom E (k.comp q) :=
      hk.1.comp (F.isDeltaHom_quotient_mk J (F.isStable_deltaClosure I))
    have hkC : (k.comp q).comp MvPolynomial.C = f := by
      rw [RingHom.comp_assoc]
      exact hk.2.1
    have hkgen : ∀ s : σ, (k.comp q) (MvPolynomial.X (s, 0)) = a s := hk.2.2
    obtain ⟨l, _, hlu⟩ := existsUnique_relativeFreeDeltaHom D E f hf a
    have hcomp : k.comp q = t :=
      (hlu (k.comp q) ⟨hkδ, hkC, hkgen⟩).trans (hlu t ⟨ht, htC, htgen⟩).symm
    exact hgu k ⟨hcomp, hk.1⟩

end SerrePositivity.BhattScholze

end RelativeFreePresentation

/-! ## 相対自由δ環の初期変数と後続変数の分離

台多項式環の同型。後続変数のδ段番号は一つ繰り下げる。
δ構造の保存や商・完備化の平坦性をこの同型だけからは主張しない。
-/

section RelativeFreeVariableSplit

namespace SerrePositivity.BhattScholze
variable (σ : Type u) (A : Type v) [CommRing A]

/-- 初期段を右項へ、後続段を左項へ分ける添字同値。 -/
def relativeFreeVariableSplit : σ × ℕ ≃ (σ × ℕ) ⊕ σ where
  toFun z := match z.2 with
    | 0 => Sum.inr z.1
    | n + 1 => Sum.inl (z.1, n)
  invFun z := match z with
    | Sum.inl (s, n) => (s, n + 1)
    | Sum.inr s => (s, 0)
  left_inv z := by obtain ⟨s, n⟩ := z; cases n <;> rfl
  right_inv z := by cases z with
    | inl z => obtain ⟨s, n⟩ := z; rfl
    | inr s => rfl

/-- 初期段の添字は係数側の変数へ送られる。 -/
@[simp] theorem relativeFreeVariableSplit_zero (s : σ) :
    relativeFreeVariableSplit σ (s, 0) = Sum.inr s := rfl

/-- 後続段の添字は外側の変数へ送られる。 -/
@[simp] theorem relativeFreeVariableSplit_succ (s : σ) (n : ℕ) :
    relativeFreeVariableSplit σ (s, n + 1) = Sum.inl (s, n) := rfl

/-- 相対自由環は初期変数の多項式環上の、後続変数の多項式環。 -/
def relativeFreeVariableSplitAlgEquiv :
    RelativeFreeDeltaRing (R := A) σ ≃ₐ[A] MvPolynomial (σ × ℕ) (MvPolynomial σ A) :=
  (MvPolynomial.renameEquiv A (relativeFreeVariableSplit σ)).trans
    (MvPolynomial.sumAlgEquiv A (σ × ℕ) σ)

/-- 変数分離は元の係数を二重の係数射へ送る。 -/
@[simp] theorem relativeFreeVariableSplitAlgEquiv_C (a : A) :
    relativeFreeVariableSplitAlgEquiv σ A (MvPolynomial.C a) =
      MvPolynomial.C (MvPolynomial.C a) := by
  simp [relativeFreeVariableSplitAlgEquiv]

/-- 初期変数は係数多項式の変数となる。 -/
@[simp] theorem relativeFreeVariableSplitAlgEquiv_X_zero (s : σ) :
    relativeFreeVariableSplitAlgEquiv σ A (MvPolynomial.X (s, 0)) =
      MvPolynomial.C (MvPolynomial.X s) := by
  simp [relativeFreeVariableSplitAlgEquiv]

/-- 後続δ変数は外側の変数となる。 -/
@[simp] theorem relativeFreeVariableSplitAlgEquiv_X_succ (s : σ) (n : ℕ) :
    relativeFreeVariableSplitAlgEquiv σ A (MvPolynomial.X (s, n + 1)) =
      MvPolynomial.X (s, n) := by
  simp [relativeFreeVariableSplitAlgEquiv]

/-- 初期変数だけの多項式の標準包含。 -/
def relativeFreeInitialPolynomialMap : MvPolynomial σ A →ₐ[A] RelativeFreeDeltaRing (R := A) σ :=
  MvPolynomial.rename (fun s => (s, 0))

/-- 後続変数だけの多項式の標準包含。 -/
def relativeFreeSuccessorPolynomialMap :
    MvPolynomial (σ × ℕ) A →ₐ[A] RelativeFreeDeltaRing (R := A) σ :=
  MvPolynomial.rename (fun z => (z.1, z.2 + 1))

/-- 初期多項式の包含は変数分離で係数射となる。 -/
theorem relativeFreeVariableSplitAlgEquiv_initial (f : MvPolynomial σ A) :
    relativeFreeVariableSplitAlgEquiv σ A (relativeFreeInitialPolynomialMap σ A f) =
      MvPolynomial.C f := by
  have he : (relativeFreeVariableSplitAlgEquiv σ A).toRingHom.comp
      (relativeFreeInitialPolynomialMap σ A).toRingHom =
      (MvPolynomial.C : MvPolynomial σ A →+* MvPolynomial (σ × ℕ) (MvPolynomial σ A)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [relativeFreeInitialPolynomialMap]
    · intro s
      simp [relativeFreeInitialPolynomialMap]
  exact RingHom.congr_fun he f

/-- 後続多項式の包含は変数分離で係数の包含による写像となる。 -/
theorem relativeFreeVariableSplitAlgEquiv_successor (f : MvPolynomial (σ × ℕ) A) :
    relativeFreeVariableSplitAlgEquiv σ A (relativeFreeSuccessorPolynomialMap σ A f) =
      MvPolynomial.map (MvPolynomial.C : A →+* MvPolynomial σ A) f := by
  have he : (relativeFreeVariableSplitAlgEquiv σ A).toRingHom.comp
      (relativeFreeSuccessorPolynomialMap σ A).toRingHom =
      MvPolynomial.map (MvPolynomial.C : A →+* MvPolynomial σ A) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [relativeFreeSuccessorPolynomialMap]
    · intro z
      obtain ⟨s, n⟩ := z
      simp [relativeFreeSuccessorPolynomialMap]
  exact RingHom.congr_fun he f

/-- 分離同型の逆は二重係数を元の係数へ戻す。 -/
@[simp] theorem relativeFreeVariableSplitAlgEquiv_symm_C_C (a : A) :
    (relativeFreeVariableSplitAlgEquiv σ A).symm (MvPolynomial.C (MvPolynomial.C a)) =
      MvPolynomial.C a := by
  apply (relativeFreeVariableSplitAlgEquiv σ A).injective
  simp

/-- 分離同型の逆は係数側変数を初期変数へ戻す。 -/
@[simp] theorem relativeFreeVariableSplitAlgEquiv_symm_C_X (s : σ) :
    (relativeFreeVariableSplitAlgEquiv σ A).symm (MvPolynomial.C (MvPolynomial.X s)) =
      MvPolynomial.X (s, 0) := by
  apply (relativeFreeVariableSplitAlgEquiv σ A).injective
  simp

/-- 分離同型の逆は外側変数を後続δ変数へ戻す。 -/
@[simp] theorem relativeFreeVariableSplitAlgEquiv_symm_X (s : σ) (n : ℕ) :
    (relativeFreeVariableSplitAlgEquiv σ A).symm (MvPolynomial.X (s, n)) =
      MvPolynomial.X (s, n + 1) := by
  apply (relativeFreeVariableSplitAlgEquiv σ A).injective
  simp

end SerrePositivity.BhattScholze

end RelativeFreeVariableSplit

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Notation 2.8"] _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing
attribute [cite BS19 "Notation 2.8"] _root_.SerrePositivity.BhattScholze.existsUnique_relativeFreeDeltaHom
attribute [cite BS19 "Notation 2.8"] _root_.SerrePositivity.BhattScholze.existsUnique_relativeFreePresentationHom
