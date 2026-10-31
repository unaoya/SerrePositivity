module

public import SerrePositivity.Asymptotic.SmallLengthSerreQuotient
public import SerrePositivity.Asymptotic.SequenceResolution
public import SerrePositivity.Asymptotic.SequenceHomology
public import SerrePositivity.PerfectComplex.Free.Euler

/-!
# 通常の長さの heart と一様自由分解の接続

通常の長さを指定した台のイデアルに制限して、長さで制限された加群列の圏を作る。
その各対象を、共通の次数幅をもつ支持つき自由列で分解する。
通常の `o(s)` 対象については、各項のランクも `o(s)` となる。
これは heart での持ち上げであり、比較関手の充満性はまだ主張しない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits IsLocalRing Filter Asymptotics
open scoped ENNReal

variable {A : Type u} [CommRing A]

/-- 指定した台のイデアル上で使う通常の長さ。値は通常の加群の長さと同じ。 -/
noncomputable def ordinaryLengthOnIdeal (J : Ideal A) : NormalizedLength A J :=
  (NormalizedLength.ordinary A).restrict J (fun M _ _ _ ↦ IsPowTorsion.bot (M := M))

@[simp] lemma ordinaryLengthOnIdeal_len (J : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] :
    (ordinaryLengthOnIdeal J).len M = (Module.length A M : ℝ≥0∞) := rfl

/-- heart の加群列の各段は有限長。 -/
lemma ordinaryLengthSequence_finite {J : Ideal A} {s : ℕ → ℕ}
    (M : LengthBoundedSequence (ordinaryLengthOnIdeal J) s) (n : ℕ) :
    IsFiniteLength A (M.obj.obj ⟨n⟩) :=
  Module.length_ne_top_iff.mp (ENat.toENNReal_ne_top.mp (M.property.2.1 n))

/-- heart の長さの条件を、自由分解の階数評価に用いる自然数値の長さに直す。 -/
lemma ordinaryLengthSequence_isBigO {J : Ideal A} {s : ℕ → ℕ}
    (M : LengthBoundedSequence (ordinaryLengthOnIdeal J) s) :
    (fun n : ℕ ↦ ((Module.length A (M.obj.obj ⟨n⟩)).toNat : ℝ)) =O[atTop]
      (fun n ↦ (s n : ℝ)) := by
  simpa only [ordinaryLengthOnIdeal_len, toReal_toENNReal] using M.property.2.2

variable [IsLocalRing A] {s : ℕ → ℕ} {e : ℕ} (z : Fin e → A)
  (K : CochainComplex (ModuleCat.{u} A) ℤ)
  (hK : IsResolutionOf K (ModuleCat.of A (A ⧸ maximalIdeal A)))
  (hKf : ∀ i, Module.Free A (K.X i)) (hKn : ∀ i, Module.Finite A (K.X i))
  (d : ℕ) (hKb : ∀ i, i < -(d : ℤ) → IsZero (K.X i))

include hK hKf hKn hKb in
/-- 実際の heart の各対象に、一様に支持された共通有界自由分解を与える。 -/
theorem ordinaryHeart_has_supported_resolution
    (M : LengthBoundedSequence (ordinaryLengthOnIdeal (Ideal.span (Set.range z))) s) :
    ∃ (F : CochainComplex (FreeSequence A s) ℤ)
      (ha : F.IsStrictlyGE (-(d : ℤ))) (hb : F.IsStrictlyLE 0),
      (∀ n, Nonempty (IsResolutionOf ((evaluateComplex n).obj F) (M.obj.obj ⟨n⟩))) ∧
      supportedSequence z (sequenceHomotopyObj F ⟨-(d : ℤ), 0, ha, hb⟩) ∧
      ∀ i n, (F.X i).rank n =
        (Module.length A (M.obj.obj ⟨n⟩)).toNat * Module.finrank A (K.X i) := by
  obtain ⟨F, ⟨ha, hb⟩, hres, hrank⟩ := exists_sequence_resolution K hK hKf hKn d hKb
    (fun n ↦ M.obj.obj ⟨n⟩) (ordinaryLengthSequence_finite M) (ordinaryLengthSequence_isBigO M)
  obtain ⟨k, hk⟩ := M.property.1
  refine ⟨F, ha, hb, hres, ?_, hrank⟩
  apply sequence_resolution_supported z F d ha hb _ hres (k + 1) (by omega)
  intro n j
  have hz : z j ^ k ∈ Module.annihilator A (M.obj.obj ⟨n⟩) :=
    hk n (Ideal.pow_mem_pow (Ideal.subset_span (show z j ∈ Set.range z from ⟨j, rfl⟩)) k)
  ext x
  change z j ^ (k + 1) • x = 0
  rw [pow_succ', mul_smul, Module.mem_annihilator.mp hz x, smul_zero]

/-- 上の分解の第零ホモロジーは、元の加群列に同型。 -/
noncomputable def sequenceResolutionHomologyZeroIso
    (M : ModuleSequence A) (F : CochainComplex (FreeSequence A s) ℤ)
    (hF : strictlyBoundedComplex (FreeSequence A s) F)
    (hres : ∀ n, Nonempty (IsResolutionOf ((evaluateComplex n).obj F) (M.obj ⟨n⟩))) :
    (sequenceHomology 0).obj (sequenceHomotopyObj F hF) ≅ M :=
  sequenceHomologyComplexIso F hF 0 ≪≫ Discrete.natIso (fun n ↦ (hres n.as).some.homologyZeroIso)

omit [IsLocalRing A] in
/-- 分解の他の次数のホモロジーは、加群列の圏でも零。 -/
lemma sequenceResolutionHomology_isZero
    (M : ModuleSequence A) (F : CochainComplex (FreeSequence A s) ℤ)
    (hF : strictlyBoundedComplex (FreeSequence A s) F)
    (hres : ∀ n, Nonempty (IsResolutionOf ((evaluateComplex n).obj F) (M.obj ⟨n⟩)))
    (q : ℤ) (hq : q ≠ 0) : IsZero ((sequenceHomology q).obj (sequenceHomotopyObj F hF)) := by
  apply IsZero.of_iso _ (sequenceHomologyComplexIso F hF q)
  rw [IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext n
  exact ((hres n.as).some.isZero_homology q hq).eq_of_src _ _

include hK hKf hKn hKb in
/-- 通常の `o(s)` の heart 対象には、小さいランクで一様に支持された自由分解がある。 -/
theorem ordinarySmallHeart_has_supported_resolution
    (M : LengthBoundedSequence (ordinaryLengthOnIdeal (Ideal.span (Set.range z))) s)
    (hM : smallSequenceLength _ s M) :
    ∃ (F : CochainComplex (FreeSequence A s) ℤ)
      (ha : F.IsStrictlyGE (-(d : ℤ))) (hb : F.IsStrictlyLE 0),
      (∀ n, Nonempty (IsResolutionOf ((evaluateComplex n).obj F) (M.obj.obj ⟨n⟩))) ∧
      supportedSequence z (sequenceHomotopyObj F ⟨-(d : ℤ), 0, ha, hb⟩) ∧ rankSmallComplex F := by
  obtain ⟨F, ha, hb, hres, hsupp, hrank⟩ :=
    ordinaryHeart_has_supported_resolution z K hK hKf hKn d hKb M
  refine ⟨F, ha, hb, hres, hsupp, ⟨-(d : ℤ), 0, ha, hb⟩, fun i ↦ ?_⟩
  have hlen : (fun n : ℕ ↦ ((Module.length A (M.obj.obj ⟨n⟩)).toNat : ℝ)) =o[atTop]
      (fun n ↦ (s n : ℝ)) := by
    simpa only [smallSequenceLength, ordinaryLengthOnIdeal_len, toReal_toENNReal] using hM
  apply (hlen.const_mul_left (Module.finrank A (K.X i) : ℝ)).congr_left
  intro n
  rw [hrank, Nat.cast_mul, mul_comm]

end SerrePositivity.Asymptotic
