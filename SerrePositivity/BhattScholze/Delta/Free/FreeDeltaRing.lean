module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.CharP.Quotient
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import Mathlib.Logic.Function.Iterate
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaQuotient

/-!
# 整数係数の自由 δ 環（BS 著者版 Lemma 2.11）と、Frobenius 持ち上げが δ 射であること

## 概要
ℤ[x_(s,n)] に φ(x_(s,n)) = x_(s,n)^p + p·x_(s,n+1) を与えて δ 構造を入れ、普遍性・表示・相対版との比較を示す。
系として任意の δ 環で φ と δ が可換、すなわち φ は δ 射（BS 著者版 Remark 2.2・Lemma 2.11 に関わる自由 δ 環の計算）。
整数上の標準 δ 構造を係数とする相対自由構成との比較を、BS 著者版 Example 2.6 と Lemma 2.11 に関わる係数計算として扱う。

## 方針
原典どおり、p ねじれなしと BS 著者版 Remark 2.2 の対応で δ 構造を作る。φ が δ 射であることは自由 δ 環で確かめて普遍性で送る。

## 規約
終域の p ねじれを許す。

## 使われ方
Frobenius の平坦性の計算（Free/FreeDeltaFrobeniusFlat）、δ 完全化、André の δ 代数の Frobenius 段。
-/

@[expose] public noncomputable section
universe u v

/-! ## 整数係数の自由δ環

変数x_(s,n)を持つ整数多項式環にφ(x_(s,n))=x_(s,n)^p+p*x_(s,n+1)を与える。
BS 著者版 Lemma 2.11の整数係数の構成。原典のZ_(p)係数への局所化と
Frobeniusの忠実平坦性は、このモジュールで完成したとはしない。
-/

section FreeDeltaRing

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (σ : Type u)

/-- 変数x_(s,n)の整数多項式環（BS 著者版 Lemma 2.11 の多項式表示の整数係数・任意変数族の場合）。
  δ^n(x_s)をx_(s,n)として実現する。 -/
abbrev FreeDeltaRing := MvPolynomial (σ × ℕ) ℤ

/-- 自由δ環のFrobenius持上げ候補。整数は固定し、各変数をx^p+p*次の変数へ送る。 -/
def freeDeltaFrobenius : FreeDeltaRing σ →+* FreeDeltaRing σ :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) (fun v ↦
    MvPolynomial.X v ^ p + (p : FreeDeltaRing σ) * MvPolynomial.X (v.1, v.2 + 1))

omit [Fact p.Prime] in
/-- 自由δ環のFrobenius候補の生成元上での値。 -/
@[simp] theorem freeDeltaFrobenius_X (s : σ) (n : ℕ) :
    freeDeltaFrobenius p σ (MvPolynomial.X (s, n)) =
      MvPolynomial.X (s, n) ^ p + (p : FreeDeltaRing σ) * MvPolynomial.X (s, n + 1) := by
  simp [freeDeltaFrobenius]

/-- 整数多項式環ではpの乗法が単射。δ構造の復元でpを消去するために使う。 -/
theorem freeDeltaRing_p_mul_injective :
    Function.Injective (fun x : FreeDeltaRing σ ↦ (p : FreeDeltaRing σ) * x) := by
  intro x y hxy
  change (p : FreeDeltaRing σ) * x = (p : FreeDeltaRing σ) * y at hxy
  exact mul_left_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero) hxy

/-- 生成元上で定めたφはmod pでFrobeniusとなる。
多項式環の準同型の外延性で整数係数と各変数を比較する。 -/
theorem freeDeltaFrobenius_mod_p (x : FreeDeltaRing σ) :
    Ideal.Quotient.mk (Ideal.span {(p : FreeDeltaRing σ)}) (freeDeltaFrobenius p σ x) =
      Ideal.Quotient.mk (Ideal.span {(p : FreeDeltaRing σ)}) x ^ p := by
  let I := Ideal.span {(p : FreeDeltaRing σ)}
  let q := Ideal.Quotient.mk I
  have hpu : ¬ IsUnit (p : FreeDeltaRing σ) := by
    intro h
    have hm := h.map (MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p))
      (fun _ : σ × ℕ ↦ 0))
    exact zero_ne_one (by
      simpa only [map_natCast, CharP.cast_eq_zero, isUnit_zero_iff] using hm)
  let : CharP (FreeDeltaRing σ ⧸ I) p := CharP.quotient (FreeDeltaRing σ) p hpu
  have hqp : q (p : FreeDeltaRing σ) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have h : q.comp (freeDeltaFrobenius p σ) = (frobenius (FreeDeltaRing σ ⧸ I) p).comp q := by
    apply MvPolynomial.ringHom_ext' (Subsingleton.elim _ _)
    intro v
    rcases v with ⟨s, n⟩
    simp only [RingHom.comp_apply, freeDeltaFrobenius_X, map_add, map_mul, map_pow,
      hqp, zero_mul, add_zero, frobenius_def]
  exact DFunLike.congr_fun h x

/-- 自由整数δ環のδ構造の存在・一意性。
p正則性とmod p Frobeniusの計算から前段の復元定理を適用する。 -/
theorem existsUnique_freeDeltaStructure :
    ∃! D : DeltaStructure p (FreeDeltaRing σ), D.frobeniusLift = freeDeltaFrobenius p σ :=
  DeltaStructure.existsUnique_of_mod_p (freeDeltaRing_p_mul_injective p σ)
    (freeDeltaFrobenius p σ) (freeDeltaFrobenius_mod_p p σ)

/-- 自由整数δ環の標準δ構造。指定したFrobeniusを持つ一意な構造として選ぶ。 -/
def freeDeltaStructure : DeltaStructure p (FreeDeltaRing σ) :=
  (existsUnique_freeDeltaStructure p σ).choose

/-- 自由整数δ環のFrobenius持上げは、生成元上で指定したφ。 -/
@[simp] theorem freeDeltaStructure_frobeniusLift :
    (freeDeltaStructure p σ).frobeniusLift = freeDeltaFrobenius p σ :=
  (existsUnique_freeDeltaStructure p σ).choose_spec.1

/-- δ(x_(s,n))=x_(s,n+1)。Frobeniusの式からpを消去する。 -/
@[simp] theorem freeDeltaStructure_delta_X (s : σ) (n : ℕ) :
    (freeDeltaStructure p σ).delta (MvPolynomial.X (s, n)) = MvPolynomial.X (s, n + 1) := by
  apply freeDeltaRing_p_mul_injective p σ
  apply add_left_cancel (a := MvPolynomial.X (s, n) ^ p)
  rw [← DeltaStructure.frobeniusLift_apply, freeDeltaStructure_frobeniusLift,
    freeDeltaFrobenius_X]

end SerrePositivity.BhattScholze

end FreeDeltaRing

/-! ## 自由整数δ環の普遍性

任意のδ環と生成元の指定から、δの反復像を座標へ評価する一意なδ射を構成する。
BS 著者版 Lemma 2.11の整数係数の普遍性。pねじれを持つ終域も許す。
-/

section FreeDeltaUniversal

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {σ : Type u} {A : Type v} [CommRing A]

/-- 指定した元族の反復δ像へ、自由環の各座標を評価する環準同型。 -/
def freeDeltaEval (D : DeltaStructure p A) (a : σ → A) : FreeDeltaRing σ →+* A :=
  MvPolynomial.eval₂Hom (Int.castRingHom A) (fun v ↦ D.delta^[v.2] (a v.1))

/-- 自由δ環の評価射はx_(s,n)をδ^n(a_s)へ送る。 -/
@[simp] theorem freeDeltaEval_X (D : DeltaStructure p A) (a : σ → A) (s : σ) (n : ℕ) :
    freeDeltaEval D a (MvPolynomial.X (s, n)) = D.delta^[n] (a s) := by
  simp [freeDeltaEval]

/-- 自由δ環の評価射はδと可換。W₂切断の二つの環準同型を生成元上で比較する。
終域のp正則性は仮定せず、単なるFrobenius可換性だけでδ射と判定しない。 -/
theorem freeDeltaEval_isDeltaHom (D : DeltaStructure p A) (a : σ → A) :
    (freeDeltaStructure p σ).IsDeltaHom D (freeDeltaEval D a) := by
  apply DeltaStructure.isDeltaHom_mvPolynomial_of_sectionHom_comp_C _ _ _
    (Subsingleton.elim _ _)
  rintro ⟨s, n⟩
  rw [freeDeltaStructure_delta_X, freeDeltaEval_X, freeDeltaEval_X,
    Function.iterate_succ_apply']

/-- 自由δ環からのδ射の生成元像は、初期座標の像の反復δとなる。 -/
theorem freeDeltaHom_X_iterates (D : DeltaStructure p A) (f : FreeDeltaRing σ →+* A)
    (hf : (freeDeltaStructure p σ).IsDeltaHom D f) (s : σ) (n : ℕ) :
    f (MvPolynomial.X (s, n)) = D.delta^[n] (f (MvPolynomial.X (s, 0))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [← freeDeltaStructure_delta_X p σ s n, hf, ih, Function.iterate_succ_apply']

/-- 任意のδ環と元族a_sについて、x_(s,0)をa_sへ送るδ射が一意に存在する（BS 著者版 Lemma 2.11 の自由性の整数係数・任意変数族の場合）。
整数係数の自由δ環の普遍性。 -/
theorem existsUnique_freeDeltaHom (D : DeltaStructure p A) (a : σ → A) :
    ∃! f : FreeDeltaRing σ →+* A,
      (freeDeltaStructure p σ).IsDeltaHom D f ∧
        ∀ s : σ, f (MvPolynomial.X (s, 0)) = a s := by
  refine ⟨freeDeltaEval D a, ⟨freeDeltaEval_isDeltaHom D a, ?_⟩, ?_⟩
  · intro s
    simp
  · intro f hf
    apply MvPolynomial.ringHom_ext' (Subsingleton.elim _ _)
    rintro ⟨s, n⟩
    rw [freeDeltaHom_X_iterates D f hf.1 s n, hf.2 s, freeDeltaEval_X]

end SerrePositivity.BhattScholze

end FreeDeltaUniversal

/-! ## 自由δ環に関係式を課す普遍性

自由整数δ環のイデアルIのδ閉包による商は、Iを零に送るδ射の普遍対象である。
BS 著者版 Notation 2.8・BS 著者版 Example 2.10の生成元と関係式の代数的構成。
完備化やprismatic envelopeそのものはこのモジュールには含まない。
-/

section FreeDeltaPresentation

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {σ : Type u} {A : Type v} [CommRing A]

/-- 元族a_sへの評価がIを零に送れば、自由δ環のδ閉包商から、
初期生成元をa_sへ送るδ射が一意に存在する。具体的な商構造・標準写像を明示する。 -/
theorem existsUnique_freeDeltaPresentationHom (D : DeltaStructure p A) (a : σ → A)
    (I : Ideal (FreeDeltaRing σ)) (hI : ∀ r ∈ I, freeDeltaEval D a r = 0) :
    ∃! g : (FreeDeltaRing σ ⧸ (freeDeltaStructure p σ).deltaClosure I) →+* A,
      ((freeDeltaStructure p σ).quotient ((freeDeltaStructure p σ).deltaClosure I)
        ((freeDeltaStructure p σ).isStable_deltaClosure I)).IsDeltaHom D g ∧
      ∀ s : σ, g (Ideal.Quotient.mk ((freeDeltaStructure p σ).deltaClosure I)
        (MvPolynomial.X (s, 0))) = a s := by
  let F := freeDeltaStructure p σ
  let J := F.deltaClosure I
  let Q := F.quotient J (F.isStable_deltaClosure I)
  let q := Ideal.Quotient.mk J
  let f := freeDeltaEval D a
  have hf : F.IsDeltaHom D f := freeDeltaEval_isDeltaHom D a
  have hker : I ≤ RingHom.ker f := fun r hr ↦ hI r hr
  obtain ⟨g, hg, hgu⟩ := F.existsUnique_deltaClosure_quotient_lift I D f hf hker
  refine ⟨g, ⟨hg.2, ?_⟩, ?_⟩
  · intro s
    have h := DFunLike.congr_fun hg.1 (MvPolynomial.X (s, 0))
    exact h.trans (by simp [f])
  · intro k hk
    have hkδ : F.IsDeltaHom D (k.comp q) :=
      hk.1.comp (F.isDeltaHom_quotient_mk J (F.isStable_deltaClosure I))
    have hkgen : ∀ s : σ, (k.comp q) (MvPolynomial.X (s, 0)) = a s := hk.2
    have hfg : ∀ s : σ, f (MvPolynomial.X (s, 0)) = a s := by
      intro s
      simp [f]
    obtain ⟨l, _, hlu⟩ := existsUnique_freeDeltaHom D a
    have hcomp : k.comp q = f :=
      (hlu (k.comp q) ⟨hkδ, hkgen⟩).trans (hlu f ⟨hf, hfg⟩).symm
    exact hgu k ⟨hcomp, hk.1⟩

end SerrePositivity.BhattScholze

end FreeDeltaPresentation

/-! ## 相対自由構成と自由整数δ環の比較

基底が整数環の場合、相対W₂切断によるδ構造と、前段のFrobenius持上げによる
自由整数δ構造は一致する。二つの構成を互換なAPIとして利用するための比較。
-/

section RelativeFreeIntegerComparison

namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (σ : Type u)

/-- 整数上の相対自由δ構造は既存の自由整数δ構造と一致する。
Frobeniusを係数・変数上で比較し、整数多項式環のp正則性による一意性を使う。 -/
theorem relativeFreeDeltaStructure_int_eq (D : DeltaStructure p ℤ) :
    relativeFreeDeltaStructure σ D = freeDeltaStructure p σ := by
  have hφ : (relativeFreeDeltaStructure σ D).frobeniusLift = freeDeltaFrobenius p σ := by
    apply MvPolynomial.ringHom_ext' (Subsingleton.elim _ _)
    rintro ⟨s, n⟩
    rw [DeltaStructure.frobeniusLift_apply, relativeFreeDeltaStructure_delta_X,
      freeDeltaFrobenius_X]
  exact (existsUnique_freeDeltaStructure p σ).choose_spec.2 _ hφ

end SerrePositivity.BhattScholze

end RelativeFreeIntegerComparison

/-! ## pねじれを許すFrobeniusのδ射性

自由整数δ環のp正則性で確認した恒等式を任意のδ環へ評価する。
完全化の反復図式に追加のp正則性を要求しない。
-/

section DeltaFrobeniusNaturality

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 任意のδ環でFrobenius持上げとδは可換。 -/
theorem frobeniusLift_delta (D : DeltaStructure p A) (x : A) :
    D.frobeniusLift (D.delta x) = D.delta (D.frobeniusLift x) := by
  let F := freeDeltaStructure p Unit
  let f := freeDeltaEval D (fun _ : Unit ↦ x)
  have hf : F.IsDeltaHom D f := freeDeltaEval_isDeltaHom D (fun _ : Unit ↦ x)
  let t : FreeDeltaRing Unit := MvPolynomial.X ((), 0)
  have ht : f t = x := by simp [f, t]
  have h := congrArg f (isDeltaHom_of_map_frobeniusLift (D := F) (E := F) F.frobeniusLift
    (freeDeltaRing_p_mul_injective p Unit) (fun _ ↦ rfl) t)
  rw [hf.map_frobeniusLift, hf, hf, hf.map_frobeniusLift, ht] at h
  exact h

/-- 任意のδ環のFrobenius持上げはδ射。p正則性を要求しない版。 -/
theorem isDeltaHom_frobeniusLift_general (D : DeltaStructure p A) :
    D.IsDeltaHom D D.frobeniusLift := D.frobeniusLift_delta

/-- Frobeniusの全ての反復はδと可換。 -/
theorem frobeniusLift_iterate_delta (D : DeltaStructure p A) (n : ℕ) (x : A) :
    (D.frobeniusLift : A → A)^[n] (D.delta x) =
      D.delta ((D.frobeniusLift : A → A)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, D.frobeniusLift_delta]

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaFrobeniusNaturality

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 2.11" (partial := special) "係数は Z（原典は Z_(p)）、多項式環としての記述と普遍性。Frobenius は mod p で自由・忠実平坦、p 完全忠実平坦まで（「本当の忠実平坦性は述べない」）。Q{x} の主張は未 ／ DOC1 照合：ok 4 件"] _root_.SerrePositivity.BhattScholze.FreeDeltaRing
attribute [cite BS19 "Lemma 2.11" (partial := special) "係数は Z（原典は Z_(p)）、多項式環としての記述と普遍性。Frobenius は mod p で自由・忠実平坦、p 完全忠実平坦まで（「本当の忠実平坦性は述べない」）。Q{x} の主張は未 ／ DOC1 照合：ok 4 件"] _root_.SerrePositivity.BhattScholze.existsUnique_freeDeltaHom
