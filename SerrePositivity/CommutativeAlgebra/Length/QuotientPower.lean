module

public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.CommutativeAlgebra.Koszul.Powers

/-! # 冪で割った商の長さ

## 概要

イデアルや正則列の冪で割った商の長さを、冪の指数と元の商の長さで評価する
（`length_quotSMulTop_pow`、`length_quotient_regularSequence_powers` など）。

## 方針

正則元 `x` について `R/x^n` は `R/x` の `n` 個の拡大なので長さが `n` 倍になる。正則列はその反復。

## 規約

長さは `Module.length`。

## 使われ方

根の塔の長さの評価（`LengthAlgebra`）とパラメータの冪の重複度。
-/

public noncomputable section

universe u v w

section QuotientPower

namespace SerrePositivity

variable (R : Type u) [CommRing R]

/-- 積xyを関係式に持つ商から、yを関係式に持つ商への自然な射を定める包含。 -/
theorem quotientSupSpanMul_le (I : Ideal R) (x y : R) :
    I ⊔ Ideal.span {x * y} ≤ I ⊔ Ideal.span {y} := by
  apply sup_le le_sup_left
  rw [Ideal.span_le]
  rintro _ rfl
  exact (show Ideal.span {y} ≤ I ⊔ Ideal.span {y} from le_sup_right)
    (Ideal.mul_mem_left _ x (Ideal.subset_span (Set.mem_singleton y)))

/-- 右完全列の最初の射：y倍によって、xの関係式をxyの関係式へ送る。 -/
def quotientSupSpanMulMap (I : Ideal R) (x y : R) :
    R ⧸ (I ⊔ Ideal.span {x}) →ₗ[R] R ⧸ (I ⊔ Ideal.span {x * y}) := by
  let J := I ⊔ Ideal.span {x * y}
  let X := I ⊔ Ideal.span {x}
  let m : R →ₗ[R] R ⧸ J := (LinearMap.lsmul R (R ⧸ J) y).comp J.mkQ
  have hm : X ≤ LinearMap.ker m := by
    intro a ha
    obtain ⟨b, c, hc, rfl⟩ := (Ideal.mem_span_singleton_sup.mp (by
      simpa only [X, sup_comm] using ha))
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change y * (b * x + c) ∈ J
    rw [mul_add]
    apply J.add_mem
    · have hh : x * y ∈ J := (show Ideal.span {x * y} ≤ J from le_sup_right)
        (Ideal.subset_span (Set.mem_singleton _))
      convert J.mul_mem_left b hh using 1
      ring
    · exact (show I ≤ J from le_sup_left) (I.mul_mem_left y hc)
  exact X.liftQ m hm

/-- 右完全列の二番目の射：yを関係式へ追加する自然な商写像。 -/
def quotientSupSpanMulProjection (I : Ideal R) (x y : R) :
    R ⧸ (I ⊔ Ideal.span {x * y}) →ₗ[R] R ⧸ (I ⊔ Ideal.span {y}) :=
  (Ideal.Quotient.factorₐ R (quotientSupSpanMul_le R I x y)).toLinearMap

/-- y倍写像と自然な商写像は完全列をなす。零因子に関する仮定は不要。 -/
theorem quotientSupSpanMul_exact (I : Ideal R) (x y : R) :
    Function.Exact (quotientSupSpanMulMap R I x y)
      (quotientSupSpanMulProjection R I x y) := by
  let J := I ⊔ Ideal.span {x * y}
  let X := I ⊔ Ideal.span {x}
  let Y := I ⊔ Ideal.span {y}
  let f := quotientSupSpanMulMap R I x y
  let g := quotientSupSpanMulProjection R I x y
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  constructor
  · intro ha
    have ha' : a ∈ Y := Ideal.Quotient.eq_zero_iff_mem.mp ha
    obtain ⟨b, c, hc, rfl⟩ := (Ideal.mem_span_singleton_sup.mp (by
      simpa only [Y, sup_comm] using ha'))
    refine ⟨Ideal.Quotient.mk X b, ?_⟩
    change Ideal.Quotient.mk J (y * b) = Ideal.Quotient.mk J (b * y + c)
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ((show I ≤ J from le_sup_left) hc),
      add_zero, mul_comm]
  · rintro ⟨b, hb⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← hb]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (show Ideal.span {y} ≤ Y from le_sup_right)
      (Ideal.mul_mem_right b _ (Ideal.subset_span (Set.mem_singleton y)))

/-- 一つの生成元を積xyにすると、商の長さはxとyの場合の長さの和以下。 -/
theorem length_quotient_sup_span_mul_le (I : Ideal R) (x y : R) :
    Module.length R (R ⧸ (I ⊔ Ideal.span {x * y})) ≤
      Module.length R (R ⧸ (I ⊔ Ideal.span {x})) +
        Module.length R (R ⧸ (I ⊔ Ideal.span {y})) := by
  let f := quotientSupSpanMulMap R I x y
  let g := quotientSupSpanMulProjection R I x y
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
    (Submodule.subtype_injective _)
    (Ideal.Quotient.factor_surjective (quotientSupSpanMul_le R I x y))
    (LinearMap.exact_subtype_ker_map g)]
  apply add_le_add _ le_rfl
  rw [LinearMap.exact_iff.mp (quotientSupSpanMul_exact R I x y)]
  exact Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict

/-- 一つの生成元を `n` 乗すると、商の長さは高々 `n` 倍になる。
零乗の場合も含み、零因子に関する仮定は要らない。 -/
theorem length_quotient_sup_span_pow_le (I : Ideal R) (x : R) (n : ℕ) :
    Module.length R (R ⧸ (I ⊔ Ideal.span {x ^ n})) ≤
      n * Module.length R (R ⧸ (I ⊔ Ideal.span {x})) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ ≤ Module.length R (R ⧸ (I ⊔ Ideal.span {x ^ n})) +
            Module.length R (R ⧸ (I ⊔ Ideal.span {x})) := by
          rw [pow_succ]
          exact length_quotient_sup_span_mul_le R I (x ^ n) x
        _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
          add_le_add ih (le_refl (Module.length R (R ⧸ (I ⊔ Ideal.span {x}))))

/-- `r` 個の生成元を一斉に `q` 乗した商の長さは、高々元の長さの `q^r` 倍。
任意の固定イデアル `I` を残せるので、非零元 `g` で割った環にも直接使える。 -/
theorem length_quotient_sup_span_powers_le (I : Ideal R) {r : ℕ} (z : Fin r → R) (q : ℕ) :
    Module.length R (R ⧸ (I ⊔ Ideal.span (Set.range fun i ↦ z i ^ q))) ≤
      (q : ℕ∞) ^ r * Module.length R (R ⧸ (I ⊔ Ideal.span (Set.range z))) := by
  induction r generalizing I with
  | zero =>
      have he : (fun i : Fin 0 ↦ z i ^ q) = z := funext fun i ↦ Fin.elim0 i
      rw [he, pow_zero, one_mul]
  | succ r ih =>
      rw [Fin.range_fin_succ (fun i ↦ z i ^ q), Ideal.span_insert,
        ← sup_assoc, sup_right_comm I]
      calc
        _ ≤ (q : ℕ∞) * Module.length R
            (R ⧸ ((I ⊔ Ideal.span (Set.range fun i : Fin r ↦ z i.succ ^ q)) ⊔
              Ideal.span {z 0})) := length_quotient_sup_span_pow_le R _ _ q
        _ = (q : ℕ∞) * Module.length R
            (R ⧸ ((I ⊔ Ideal.span {z 0}) ⊔
              Ideal.span (Set.range fun i : Fin r ↦ z i.succ ^ q))) := by
          rw [sup_right_comm I]
        _ ≤ (q : ℕ∞) * ((q : ℕ∞) ^ r * Module.length R
            (R ⧸ ((I ⊔ Ideal.span {z 0}) ⊔ Ideal.span (Set.range fun i : Fin r ↦ z i.succ)))) :=
          mul_le_mul_right (ih (I ⊔ Ideal.span {z 0}) (fun i ↦ z i.succ)) _
        _ = _ := by
          rw [Fin.range_fin_succ z, Ideal.span_insert, ← sup_assoc, pow_succ, mul_assoc]
          ac_rfl

/-- `H` 内の `r` 個の元を用いて、Frobenius 冪と固定イデアル `I` で割った商を評価する。
特に `I = (g)` とすれば、共通分母から生じる誤差項の成長評価になる。 -/
theorem length_quotient_frobenius_sup_le (I H : Ideal R) {r : ℕ} (z : Fin r → R)
    (hz : ∀ i, z i ∈ H) (p : ℕ) [ExpChar R p] (n : ℕ) :
    Module.length R (R ⧸ (H.map (iterateFrobenius R p n) ⊔ I)) ≤
      ((p ^ n : ℕ) : ℕ∞) ^ r * Module.length R (R ⧸ (I ⊔ Ideal.span (Set.range z))) := by
  have hle : I ⊔ Ideal.span (Set.range fun i ↦ z i ^ (p ^ n)) ≤
      H.map (iterateFrobenius R p n) ⊔ I := by
    apply sup_le le_sup_right
    apply le_trans _ le_sup_left
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_map_of_mem (iterateFrobenius R p n) (hz i)
  exact (Module.length_le_of_surjective (Ideal.Quotient.factorₐ R hle).toLinearMap
    (Ideal.Quotient.factor_surjective hle)).trans
    (length_quotient_sup_span_powers_le R I z (p ^ n))

/-- 固定イデアルと `H` 内の有限個の元で割った商が有限長なら、
`H` のどの Frobenius 冪を使った商も有限長である。上の数値評価から従う。 -/
theorem isFiniteLength_quotient_frobenius_sup (I H : Ideal R) {r : ℕ} (z : Fin r → R)
    (hz : ∀ i, z i ∈ H) (hfin : IsFiniteLength R (R ⧸ (I ⊔ Ideal.span (Set.range z))))
    (p : ℕ) [ExpChar R p] (n : ℕ) :
    IsFiniteLength R (R ⧸ (H.map (iterateFrobenius R p n) ⊔ I)) := by
  apply Module.length_ne_top_iff.mp
  apply ne_top_of_le_ne_top _ (length_quotient_frobenius_sup_le R I H z hz p n)
  exact WithTop.mul_ne_top (WithTop.pow_ne_top (ENat.natCast_ne_top (p ^ n)))
    (Module.length_ne_top_iff.mpr hfin)

/-- Frobenius 冪イデアルの根基は元のイデアルの根基に等しい。
一方の包含は生成元の冪が元のイデアルに入ること、逆の包含は根基の定義による。 -/
theorem radical_map_iterateFrobenius (I : Ideal R) (p : ℕ) [ExpChar R p] (n : ℕ) :
    (I.map (iterateFrobenius R p n)).radical = I.radical := by
  apply le_antisymm
  · apply Ideal.radical_mono
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact I.pow_mem_of_mem hx _ (pow_pos (expChar_pos R p) n)
  · have hle : I ≤ (I.map (iterateFrobenius R p n)).radical := by
      intro x hx
      exact Ideal.mem_radical_iff.mpr ⟨p ^ n, Ideal.mem_map_of_mem _ hx⟩
    simpa only [Ideal.radical_idem] using Ideal.radical_mono hle

/-- Noether 環では、有限長の商を定めるイデアルの Frobenius 冪も有限長の商を定める。
根基が変わらないため、Artin 性を根基の包含から移す一般論を適用できる。 -/
theorem isFiniteLength_quotient_map_iterateFrobenius [IsNoetherianRing R]
    (I : Ideal R) (hI : IsFiniteLength R (R ⧸ I)) (p : ℕ) [ExpChar R p] (n : ℕ) :
    IsFiniteLength R (R ⧸ I.map (iterateFrobenius R p n)) := by
  let : IsArtinian R (R ⧸ I) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hI).2
  let : IsArtinianRing (R ⧸ I) := isArtinian_of_tower R inferInstance
  apply isFiniteLength_of_le_radical_annihilator I
  rw [Ideal.annihilator_quotient, radical_map_iterateFrobenius]
  exact Ideal.le_radical

end SerrePositivity

end QuotientPower

section RegularSequence

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity

open scoped Pointwise
open Submodule RingTheory.Sequence

variable {R : Type*} [CommRing R]

/-- `y` が `M` 上正則なら `M/xyM` の長さは `M/xM` と `M/yM` の長さの和。 -/
theorem length_quotSMulTop_mul (M : Type*) [AddCommGroup M] [Module R M]
    (x y : R) (hy : IsSMulRegular M y) :
    Module.length R (QuotSMulTop (x * y) M) =
      Module.length R (QuotSMulTop x M) + Module.length R (QuotSMulTop y M) := by
  let X : Submodule R M := x • ⊤
  let Y : Submodule R M := y • ⊤
  let J : Submodule R M := (x * y) • ⊤
  have hJY : J ≤ Y := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := (mem_smul_pointwise_iff_exists a (x * y) ⊤).mp ha
    exact (mem_smul_pointwise_iff_exists _ y ⊤).mpr
      ⟨x • b, trivial, by rw [mul_comm x y, mul_smul]⟩
  let m : M →ₗ[R] M ⧸ J := J.mkQ.comp (LinearMap.lsmul R M y)
  have hm : X ≤ LinearMap.ker m := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := (mem_smul_pointwise_iff_exists a x ⊤).mp ha
    apply (Submodule.Quotient.mk_eq_zero J).mpr
    exact (mem_smul_pointwise_iff_exists _ (x * y) ⊤).mpr
      ⟨b, trivial, by rw [mul_comm x y, mul_smul]; rfl⟩
  let f : M ⧸ X →ₗ[R] M ⧸ J := X.liftQ m hm
  let g : M ⧸ J →ₗ[R] M ⧸ Y := Submodule.factor hJY
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply eq_bot_iff.mpr
    intro a ha
    obtain ⟨a, rfl⟩ := X.mkQ_surjective a
    have ha' : y • a ∈ J := (Submodule.Quotient.mk_eq_zero J).mp ha
    obtain ⟨b, _, hb⟩ := (mem_smul_pointwise_iff_exists _ (x * y) ⊤).mp ha'
    have hb' : x • b = a := hy (by rwa [mul_comm x y, mul_smul] at hb)
    exact (Submodule.Quotient.mk_eq_zero X).mpr
      ((mem_smul_pointwise_iff_exists a x ⊤).mpr ⟨b, trivial, hb'⟩)
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨a, rfl⟩ := Y.mkQ_surjective a
    exact ⟨J.mkQ a, rfl⟩
  have he : Function.Exact f g := by
    intro a
    obtain ⟨a, rfl⟩ := J.mkQ_surjective a
    constructor
    · intro ha
      obtain ⟨b, _, hb⟩ := (mem_smul_pointwise_iff_exists a y ⊤).mp
        ((Submodule.Quotient.mk_eq_zero Y).mp ha)
      exact ⟨X.mkQ b, congrArg J.mkQ hb⟩
    · rintro ⟨b, hb⟩
      obtain ⟨b, rfl⟩ := X.mkQ_surjective b
      rw [← hb]
      exact (Submodule.Quotient.mk_eq_zero Y).mpr
        ((mem_smul_pointwise_iff_exists _ y ⊤).mpr ⟨b, trivial, rfl⟩)
  exact Module.length_eq_add_of_exact f g hf hg he

/-- 正則なスカラーの `v` 乗で割った長さは `v` 倍。無限長も許す。 -/
theorem length_quotSMulTop_pow (M : Type*) [AddCommGroup M] [Module R M]
    (x : R) (hx : IsSMulRegular M x) (v : ℕ) :
    Module.length R (QuotSMulTop (x ^ v) M) =
      v * Module.length R (QuotSMulTop x M) := by
  induction v with
  | zero => simp [QuotSMulTop]
  | succ v ih =>
    rw [pow_succ, length_quotSMulTop_mul M (x ^ v) x hx, ih]
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- 弱正則列の各元を `v` 乗すると、商の長さは `v^(列の長さ)` 倍。 -/
theorem length_quotient_regularSequence_powers [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [IsNoetherian R M]
    {rs : List R} (h : IsWeaklyRegular M rs)
    (hm : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R) (v : ℕ) (hv : 0 < v) :
    Module.length R (M ⧸ (Ideal.ofList (rs.map (fun x ↦ x ^ v)) • ⊤ : Submodule R M)) =
      (v : ℕ∞) ^ rs.length *
        Module.length R (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M)) := by
  induction rs generalizing M with
  | nil => rw [List.length_nil, pow_zero, one_mul]; rfl
  | cons x rs ih =>
    obtain ⟨hx, hrs⟩ := (isWeaklyRegular_cons_iff M x rs).mp h
    have hmrs : ∀ y ∈ rs, y ∈ IsLocalRing.maximalIdeal R :=
      fun y hy ↦ hm y (List.mem_cons_of_mem x hy)
    let ps := rs.map (fun y ↦ y ^ v)
    have hp : IsWeaklyRegular M (x :: ps) :=
      .cons hx (isWeaklyRegular_map_pow (QuotSMulTop x M) hrs hmrs v hv)
    have hmp : ∀ y ∈ x :: ps, y ∈ IsLocalRing.maximalIdeal R := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hm y (by simp)
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
        exact (IsLocalRing.maximalIdeal R).pow_mem_of_mem (hmrs a ha) v hv
    have hlast := IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hp
      (by simpa using (List.perm_append_comm (l₁ := [x]) (l₂ := ps))) hmp
    rw [isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff] at hlast
    change Module.length R (M ⧸ (Ideal.ofList (x ^ v :: ps) • ⊤ : Submodule R M)) = _
    rw [(quotOfListConsSMulTopEquivQuotSMulTopOuter M (x ^ v) ps).length_eq,
      length_quotSMulTop_pow _ x hlast.2 v,
      ← (quotOfListConsSMulTopEquivQuotSMulTopOuter M x ps).length_eq,
      (quotOfListConsSMulTopEquivQuotSMulTopInner M x ps).length_eq,
      ih (QuotSMulTop x M) hrs hmrs,
      ← (quotOfListConsSMulTopEquivQuotSMulTopInner M x rs).length_eq]
    simp only [List.length_cons, pow_succ]
    ac_rfl

/-- `e` 個の正則な極大イデアル生成元の `v` 乗で割った長さは `v^e`。 -/
theorem length_quotient_parameter_powers [IsLocalRing R] [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R)
    (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R)
    (hreg : IsWeaklyRegular R (List.ofFn z)) (v : ℕ) (hv : 0 < v) :
    Module.length R (R ⧸ Ideal.span (Set.range fun j ↦ z j ^ v)) = (v : ℕ∞) ^ e := by
  have hm : ∀ x ∈ List.ofFn z, x ∈ IsLocalRing.maximalIdeal R := by
    intro x hx
    rw [← hz]
    exact Ideal.subset_span (by simpa only [List.mem_ofFn, Set.mem_range] using hx)
  have h := length_quotient_regularSequence_powers R hreg hm v hv
  have hspan {n : ℕ} (w : Fin n → R) : Ideal.ofList (List.ofFn w) = Ideal.span (Set.range w) := by
    apply congrArg Ideal.span
    ext x
    exact List.mem_ofFn
  have : IsSimpleModule R (R ⧸ Ideal.span (Set.range z)) :=
    isSimpleModule_quotient_span_of_eq hz
  change Module.length R (R ⧸ (Ideal.ofList ((List.ofFn z).map (fun x ↦ x ^ v)) * ⊤)) =
    (v : ℕ∞) ^ (List.ofFn z).length * Module.length R (R ⧸ (Ideal.ofList (List.ofFn z) * ⊤)) at h
  rw [List.map_ofFn, hspan, hspan, Ideal.mul_top, Ideal.mul_top] at h
  rw [show ((fun x : R ↦ x ^ v) ∘ z) = (fun j ↦ z j ^ v) from rfl] at h
  simpa only [List.length_ofFn, Module.length_eq_one, mul_one] using h

end SerrePositivity

end RegularSequence
