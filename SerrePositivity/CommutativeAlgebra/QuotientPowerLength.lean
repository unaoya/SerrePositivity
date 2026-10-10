module

public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# 生成元の冪による商の長さの評価

生成元を積に置き換えた商を二つの商で評価し、冪に関する多項式的な上界を得る。
零因子を許し、正則列・Noether 性・有限長性を仮定しない。
長さは `ℕ∞` に値を取り、有限長性が分かる場合にそのまま数値評価となる。
末尾では Frobenius 冪が根基を保つことと、Noether 環における商の有限長性の保存も示す。
-/

public section
universe u
namespace SerrePositivity

variable (R : Type u) [CommRing R]

/-- 一つの生成元を積 `xy` にすると、商の長さは `x` と `y` の場合の長さの和以下。
`y` 倍写像と自然な商写像による右完全列を使う。 -/
theorem length_quotient_sup_span_mul_le (I : Ideal R) (x y : R) :
    Module.length R (R ⧸ (I ⊔ Ideal.span {x * y})) ≤
      Module.length R (R ⧸ (I ⊔ Ideal.span {x})) +
        Module.length R (R ⧸ (I ⊔ Ideal.span {y})) := by
  let J := I ⊔ Ideal.span {x * y}
  let X := I ⊔ Ideal.span {x}
  let Y := I ⊔ Ideal.span {y}
  have hJY : J ≤ Y := by
    apply sup_le le_sup_left
    rw [Ideal.span_le]
    rintro _ rfl
    exact (show Ideal.span {y} ≤ Y from le_sup_right)
      (Ideal.mul_mem_left _ x (Ideal.subset_span (Set.mem_singleton y)))
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
  let f : R ⧸ X →ₗ[R] R ⧸ J := X.liftQ m hm
  let g : R ⧸ J →ₗ[R] R ⧸ Y := (Ideal.Quotient.factorₐ R hJY).toLinearMap
  have he : Function.Exact f g := by
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
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
    (Submodule.subtype_injective _) (Ideal.Quotient.factor_surjective hJY)
    (LinearMap.exact_subtype_ker_map g)]
  apply add_le_add _ le_rfl
  rw [LinearMap.exact_iff.mp he]
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
