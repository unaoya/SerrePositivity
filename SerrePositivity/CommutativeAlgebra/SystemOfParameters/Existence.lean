module

public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Data.Set.List
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Flat.TorsionFree
public import SerrePositivity.CommutativeAlgebra.Length.Basic

/-! # パラメータ系の存在

## 概要

Noether 局所環 `R` について：
- 根基が `m` のイデアル `I` の中から、次元個の元でパラメータ系がとれる
  （`exists_isSystemOfParameters_of_radical_eq`）。
- 極大イデアル内の非零因子 `x` から始まるパラメータ系がある（`exists_isSystemOfParameters_head_eq`）。
  `x` による商の次元は一つ下がる（`ringKrullDim_quotient_eq_of_nonZeroDivisor`）。
- イデアル `I` を法として、根基が `m` の `H` の元 `dim R/I` 個で `I` と合わせて `m` 準素にできる
  （`exists_parameters_mod_ideal_in_primary`）。次元を一つずつ下げる元が `H` にある
  （`exists_dimension_drop_in_primary`）。

## 方針

Krull の高さ定理（`Ideal.height_le_spanFinrank`）と、高さを保つ生成数の選択
（`exists_spanRank_le_and_le_height_of_le_height`）で次元個の元を選び、高さが次元に等しいことから
根基が `m` であることを得る（`SystemOfParameters/Basic`）。次元を下げる元は、極小素イデアルを
避けて素イデアル回避でとる。

## 規約

Hilbert–Samuel 理論・正則局所環の非混合性には依存しない。

## 使われ方

同標数の正規化（`EqualCharacteristicNormalization`）、混標数の Cohen 正規化（`Witt/Normalization`）、
Hilbert–Samuel 次元（`HilbertSamuelDimension`）、論文 §2 の完全商の極限（`Paper/Section2`）。
Mathlib への提出候補（mathlib-upstream の G10）。
-/

@[expose] public noncomputable section

universe u v w

open IsLocalRing PrimeSpectrum RingTheory.Sequence

namespace SerrePositivity

section Primary

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- 任意の極大イデアル準素イデアルの中から、次元個の元で生成された
極大イデアル準素イデアルを選べる。 -/
theorem exists_radical_span_eq_maximalIdeal_of_radical_eq (I : Ideal R)
    (hI : I.radical = maximalIdeal R) :
    ∃ z : Fin (dimToNat (ringKrullDim R)) → R,
      (∀ i, z i ∈ I) ∧ (Ideal.span (Set.range z)).radical = maximalIdeal R := by
  classical
  have hItop : I ≠ ⊤ := by
    intro h
    have : (⊤ : Ideal R) = maximalIdeal R := by
      rw [h, Ideal.radical_top] at hI
      exact hI
    exact (maximalIdeal.isMaximal R).ne_top this.symm
  obtain ⟨J, hJI, hJrank, hJheight⟩ := I.exists_spanRank_eq_and_height_eq hItop
  have hJtop : J ≠ ⊤ := by
    intro h
    exact hItop (top_le_iff.mp (h ▸ hJI))
  have hJdim : (J.height : WithBot ℕ∞) = ringKrullDim R := by
    rw [hJheight]
    exact height_eq_ringKrullDim_of_radical_eq_maximalIdeal I hI
  have hJprimary := (radical_eq_maximalIdeal_iff_height_eq_ringKrullDim hJtop).mpr hJdim
  obtain ⟨s, hcard, hspan⟩ :=
    (IsNoetherian.noetherian J).exists_span_finset_card_eq_spanFinrank
  have hdim : J.spanFinrank = dimToNat (ringKrullDim R) := by
    have hh : (J.spanFinrank : WithBot ℕ∞) = ringKrullDim R := by
      rw [← hJdim, hJheight]
      exact_mod_cast (Submodule.fg_iff_spanRank_eq_spanFinrank.mpr
        (IsNoetherian.noetherian J)).symm.trans hJrank
    exact_mod_cast hh.trans (natCast_dimToNat_ringKrullDim R).symm
  have hlen : s.toList.length = dimToNat (ringKrullDim R) := by
    simpa [hcard] using hdim
  let z : Fin s.toList.length → R := s.toList.get
  have hz : Ideal.span (Set.range z) = J := by simpa [z] using hspan
  rw [← hlen]
  refine ⟨z, fun i ↦ ?_, hz ▸ hJprimary⟩
  exact hJI (hz ▸ Ideal.subset_span (Set.mem_range_self i))

/-- 選んだ列は、定義どおり環のパラメータ系である。 -/
theorem exists_isSystemOfParameters_of_radical_eq (I : Ideal R)
    (hI : I.radical = maximalIdeal R) :
    ∃ z : Fin (dimToNat (ringKrullDim R)) → R,
      (∀ i, z i ∈ I) ∧ IsSystemOfParameters R z := by
  obtain ⟨z, hz, hrad⟩ := exists_radical_span_eq_maximalIdeal_of_radical_eq R I hI
  exact ⟨z, hz, (natCast_dimToNat_ringKrullDim R).symm, hrad⟩

end Primary

section Prescribed

open IsLocalRing

/-- 次元r+1のNoether局所環で、極大イデアル内の非零因子による商の次元はr。 -/
theorem ringKrullDim_quotient_eq_of_nonZeroDivisor
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ nonZeroDivisors R) (hm : x ∈ maximalIdeal R)
    {r : ℕ} (hdim : ringKrullDim R = r + 1) :
    ringKrullDim (R ⧸ Ideal.span {x}) = r := by
  have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hx)
    (ringJacobson_eq_maximalIdeal (R := R) ▸ hm)
  rw [hdim] at h
  exact le_antisymm (ENat.WithBot.add_le_add_one_right_iff.mp h.le)
    (ENat.WithBot.add_le_add_one_right_iff.mp h.ge)

/-- 指定非零因子にr個の元を加えて極大イデアル準素のイデアルを作る。
商で選んだパラメータを持ち上げ、根基の等式を商写像に沿って戻す。 -/
theorem exists_parameters_completing_nonZeroDivisor
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ nonZeroDivisors R) (hm : x ∈ maximalIdeal R)
    {r : ℕ} (hdim : ringKrullDim R = r + 1) :
    ∃ y : Fin r → R, (∀ i, y i ∈ maximalIdeal R) ∧
      (Ideal.span {x} ⊔ Ideal.span (Set.range y)).radical = maximalIdeal R := by
  classical
  let I : Ideal R := Ideal.span {x}
  have hI : I ≤ maximalIdeal R := by rwa [Ideal.span_singleton_le_iff_mem]
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
  let : IsNoetherianRing (R ⧸ I) :=
    isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.mk I
  let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hd : ringKrullDim (R ⧸ I) = r :=
    ringKrullDim_quotient_eq_of_nonZeroDivisor R x hx hm hdim
  have ht := exists_radical_span_eq_maximalIdeal_of_radical_eq
    (R ⧸ I) (maximalIdeal (R ⧸ I)) (Ideal.IsPrime.radical inferInstance)
  have hn : dimToNat (ringKrullDim (R ⧸ I)) = r := by simp [hd, dimToNat]
  rw [hn] at ht
  obtain ⟨z, hz, hrad⟩ := ht
  choose y hy using (fun i : Fin r ↦ Ideal.Quotient.mk_surjective (z i))
  have hym (i : Fin r) : y i ∈ maximalIdeal R := by
    rw [← maximalIdeal_comap q]
    change q (y i) ∈ maximalIdeal (R ⧸ I)
    rw [hy]
    exact hz i
  let J := I ⊔ Ideal.span (Set.range y)
  have hmap : J.map q = Ideal.span (Set.range z) := by
    change (I ⊔ Ideal.span (Set.range y)).map (Ideal.Quotient.mk I) = _
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span,
      ← Set.range_comp]
    rw [show (Ideal.Quotient.mk I) ∘ y = z from funext hy]
  have hcomap : (J.map q).comap q = J := by
    rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective]
    change J ⊔ RingHom.ker q = J
    rw [show RingHom.ker q = I from Ideal.mk_ker]
    exact sup_eq_left.mpr le_sup_left
  refine ⟨y, hym, ?_⟩
  change J.radical = maximalIdeal R
  calc
    J.radical = ((J.map q).radical).comap q := by rw [Ideal.comap_radical, hcomap]
    _ = (maximalIdeal (R ⧸ I)).comap q := by rw [hmap, hrad]
    _ = maximalIdeal R := maximalIdeal_comap q

/-- 指定非零因子を先頭に置いたパラメータ系。 -/
theorem exists_isSystemOfParameters_head_eq
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ nonZeroDivisors R) (hm : x ∈ maximalIdeal R)
    {r : ℕ} (hdim : ringKrullDim R = r + 1) :
    ∃ z : Fin (r + 1) → R, z 0 = x ∧ (∀ i, z i ∈ maximalIdeal R) ∧
      IsSystemOfParameters R z := by
  obtain ⟨y, hy, hrad⟩ := exists_parameters_completing_nonZeroDivisor R x hx hm hdim
  refine ⟨Fin.cons x y, Fin.cons_zero _ _, ?_, hdim, ?_⟩
  · intro i
    exact Fin.cases hm hy i
  · rw [Fin.range_cons, Ideal.span_insert]
    exact hrad

end Prescribed

section ModIdeal

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsLocalRing R] in
/-- 零次元以下の Noether 商環は、元の環上で有限長である。零環の場合も含む。 -/
theorem isFiniteLength_quotient_of_ringKrullDim_le_zero (I : Ideal R)
    (hdim : ringKrullDim (R ⧸ I) ≤ 0) : IsFiniteLength R (R ⧸ I) := by
  have : IsNoetherianRing (R ⧸ I) :=
    isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsArtinianRing (R ⧸ I) := by
    apply isArtinianRing_iff_krullDimLE_zero.mpr
    exact (Ring.krullDimLE_iff).mpr hdim
  exact isFiniteLength_of_le_radical_annihilator I (R ⧸ I) (by
    simpa only [Ideal.annihilator_quotient] using I.le_radical)

/-- 正次元の商に対し、極大イデアルを根基とする `H` の中で元を選ぶと次元を一つ下げられる。
`H` を含みうる極小素イデアルがないことと、有限素イデアル回避を使う。 -/
theorem exists_dimension_drop_in_primary (I H : Ideal R) (hH : H.radical = maximalIdeal R)
    (hpos : 0 < ringKrullDim (R ⧸ I)) :
    ∃ y ∈ H, ringKrullDim (R ⧸ (I ⊔ Ideal.span {y})) + 1 = ringKrullDim (R ⧸ I) := by
  classical
  let s := I.finite_minimalPrimes_of_isNoetherianRing.toFinset
  have hnot : ∀ p ∈ s, ¬ H ≤ p := by
    intro p hp hHp
    have hpm : p ∈ I.minimalPrimes := by simpa [s] using hp
    have hmp : maximalIdeal R ≤ p := by
      rw [← hH, ← hpm.1.1.radical]
      exact Ideal.radical_mono hHp
    have hzero : ringKrullDim (R ⧸ I) ≤ 0 := by
      rw [ringKrullDim_quotient]
      refine Order.krullDim_nonpos_iff_forall_isMax.mpr fun q q' hqq' ↦ ?_
      have hpq : p ≤ q.1.asIdeal :=
        hpm.2 ⟨q.1.isPrime, q.2⟩ ((le_maximalIdeal q.1.isPrime.ne_top).trans hmp)
      exact (le_maximalIdeal q'.1.isPrime.ne_top).trans (hmp.trans hpq)
    exact (not_lt.mpr hzero) hpos
  have hsub : ¬ ((H : Set R) ⊆ ⋃ p ∈ (↑s : Set (Ideal R)), (p : Set R)) := by
    rw [Ideal.subset_union_prime ⊥ ⊥ (fun p hp _ _ ↦ ?_)]
    · rintro ⟨p, hp, hHp⟩
      exact hnot p hp hHp
    · exact (show p ∈ I.minimalPrimes by simpa [s] using hp).1.1
  obtain ⟨y, hyH, hy⟩ := Set.not_subset.mp hsub
  simp only [Set.mem_iUnion, not_exists] at hy
  have hymin : ∀ p ∈ I.minimalPrimes, y ∉ p := by
    intro p hp
    exact hy p (by simpa [s] using hp)
  have hym : y ∈ maximalIdeal R := hH ▸ H.le_radical hyH
  have hdim := Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    (M := R ⧸ I) (by rwa [Ideal.annihilator_quotient]) hym
  rw [supportDim_quotSMulTop_quotient, Module.supportDim_quotient_eq_ringKrullDim] at hdim
  exact ⟨y, hyH, hdim⟩

/-- `dim R/I ≤ r` なら、準素イデアル `H` の中の `r` 個の元で商を有限長にできる。
次元が先に零になった場合は残りを零で埋める。 -/
theorem exists_parameters_mod_ideal_in_primary (H : Ideal R) (hH : H.radical = maximalIdeal R)
    (r : ℕ) (I : Ideal R) (hdim : ringKrullDim (R ⧸ I) ≤ r) :
    ∃ z : Fin r → R, (∀ i, z i ∈ H) ∧
      IsFiniteLength R (R ⧸ (I ⊔ Ideal.span (Set.range z))) := by
  classical
  induction r generalizing I with
  | zero =>
      refine ⟨Fin.elim0, fun i ↦ Fin.elim0 i, ?_⟩
      have he : Set.range (Fin.elim0 : Fin 0 → R) = ∅ := by simp
      rw [he, Ideal.span_empty, sup_bot_eq]
      exact isFiniteLength_quotient_of_ringKrullDim_le_zero R I hdim
  | succ r ih =>
      by_cases hpos : 0 < ringKrullDim (R ⧸ I)
      · obtain ⟨y, hy, hd⟩ := exists_dimension_drop_in_primary R I H hH hpos
        have hd' : ringKrullDim (R ⧸ (I ⊔ Ideal.span {y})) ≤ r := by
          have hh : ringKrullDim (R ⧸ (I ⊔ Ideal.span {y})) + 1 ≤ (r : WithBot ℕ∞) + 1 := by
            simpa only [hd, Nat.cast_succ] using hdim
          exact ENat.WithBot.add_le_add_one_right_iff.mp hh
        obtain ⟨z, hz, hf⟩ := ih (I ⊔ Ideal.span {y}) hd'
        refine ⟨Fin.cons y z, ?_, ?_⟩
        · intro i
          refine Fin.cases hy (fun j ↦ ?_) i
          exact hz j
        · rw [Fin.range_cons, Ideal.span_insert, ← sup_assoc]
          exact hf
      · refine ⟨fun _ ↦ 0, fun _ ↦ H.zero_mem, ?_⟩
        have he : Ideal.span (Set.range (fun _ : Fin (r + 1) ↦ (0 : R))) = ⊥ := by simp
        rw [he, sup_bot_eq]
        exact isFiniteLength_quotient_of_ringKrullDim_le_zero R I (not_lt.mp hpos)

/-- 次元 `r+1` の局所整域の非零元 `g` に対して、`H` 内の `r` 個の元と合わせて有限長の商を作れる。
非零因子による次元降下と、準素イデアル内のパラメータ選択を組み合わせる。 -/
theorem exists_error_parameters_in_primary [IsDomain R]
    (H : Ideal R) (hH : H.radical = maximalIdeal R)
    (g : R) (hg : g ≠ 0) {r : ℕ} (hdim : ringKrullDim R = r + 1) :
    ∃ z : Fin r → R, (∀ i, z i ∈ H) ∧
      IsFiniteLength R (R ⧸ (Ideal.span {g} ⊔ Ideal.span (Set.range z))) := by
  apply exists_parameters_mod_ideal_in_primary R H hH r (Ideal.span {g})
  have hd := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_iff_ne_zero.mpr hg)
  rw [hdim] at hd
  exact ENat.WithBot.add_le_add_one_right_iff.mp hd

end ModIdeal

end SerrePositivity
