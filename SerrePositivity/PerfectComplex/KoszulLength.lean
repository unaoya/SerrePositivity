module

public import SerrePositivity.PerfectComplex.Free.Euler
public import SerrePositivity.LengthAlgebra.Core
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Basic.ENNReal.BigOperators
public import SerrePositivity.HomologicalAlgebra.HomologyQuotient
public import SerrePositivity.PerfectComplex.TensorResolutionLength

/-! # Koszul ホモロジーの長さの定量評価

## 概要

§4 の列の圏で必要な一様評価を、単一の有限自由複体（有限射影項の場合は直和因子表示で）について示す：各項の基底の個数と環自身の Koszul ホモロジーの長さから、係数つき Koszul ホモロジーの長さを抑える。環自身の高次 Koszul ホモロジーの長さが零なら、Koszul 関手を施した複体の振幅は元の項の範囲に収まる。極小性から第零ホモロジーの長さの下界を与える。

## 方針

Lemma 3.5a の有限性の証明を定量化する。下界は微分の座標がイデアルに入ることから作った全射による。

## 規約

基礎環の局所性・ネーター性・有限代数性・平坦性は仮定しない。

## 使われ方

Asymptotic の複体の列の評価、Paper の §4。
-/

@[expose] public noncomputable section

universe u

section KoszulLengthBoundsPart

open CategoryTheory Limits
open scoped ENNReal BigOperators

namespace SerrePositivity

variable {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)

/-- 複体の直和因子のホモロジーの長さは元の長さ以下。
ホモロジー関手が分裂を保つことと長さの単射に対する単調性による。 -/
lemma lambdaHomology_le_of_retract {P Q : CochainComplex (ModuleCat.{u} C) ℤ}
    (h : Retract P Q) (q : ℤ) (tQ : IsPowTorsion J (Q.homology q)) :
    lam.len (P.homology q) ≤ lam.len (Q.homology q) := by
  let hh := h.map (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (ComplexShape.up ℤ) q)
  exact lam.len_le_of_injective hh.i.hom
    ((ModuleCat.mono_iff_injective hh.i).mp inferInstance) tQ

/-- 環を `a` 次に置いた場合の Koszul ホモロジーの長さは、通常の Koszul
ホモロジーの `q - a` 次の長さ。Koszul 関手とシフトの同型による。 -/
lemma lambdaHomology_koszul_single_ring_eq {n : ℕ} (x : Fin n → C) (a q : ℤ) :
    lam.len ((koszulComplexOn x
      ((HomologicalComplex.single _ _ a).obj (ModuleCat.of C C))).homology q) =
      lam.len ((koszulComplex x).homology (q - a)) := by
  let P := (HomologicalComplex.single (ModuleCat.{u} C) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of C C)
  let e := ((CochainComplex.singleFunctors (ModuleCat.{u} C)).shiftIso (-a) a 0 (by omega)).app
    (ModuleCat.of C C)
  let eK : koszulComplexOn x ((HomologicalComplex.single _ _ a).obj (ModuleCat.of C C)) ≅
      (koszulComplex x)⟦-a⟧ :=
    (koszulFunctor x).mapIso e.symm ≪≫ (koszulComplexOnShiftIso x P (-a)).symm ≪≫
      (shiftFunctor _ (-a)).mapIso (eqToIso (koszulComplexOn_single x))
  let eh :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (ComplexShape.up ℤ) q).mapIso eK ≪≫
      (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} C) (-a) q (q - a) (by omega)).app
        (koszulComplex x)
  exact lam.len_congr _ _ eh.toLinearEquiv

/-- `m` 個の環を一つの次数に置いた Koszul ホモロジーの長さは、環の場合の
`m` 倍以下。基底を一つずつ分離し、短完全列のホモロジーの不等式を反復する。 -/
lemma lambdaHomology_koszul_single_pi_le (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical) (a q : ℤ) (m : ℕ) :
    lam.len ((koszulComplexOn x
      ((HomologicalComplex.single _ _ a).obj (ModuleCat.of C (Fin m → C)))).homology q) ≤
      m • lam.len ((koszulComplex x).homology (q - a)) := by
  let F := HomologicalComplex.single (ModuleCat.{u} C) (ComplexShape.up ℤ) a ⋙ koszulFunctor x
  have ht (M : ModuleCat.{u} C) : IsPowTorsion J ((F.obj M).homology q) :=
    supported_homology_isPowTorsion hfg hJ (isSupported_koszulComplexOn x _) q
  change lam.len ((F.obj (ModuleCat.of C (Fin m → C))).homology q) ≤ _
  induction m with
  | zero =>
    have hzero : IsZero (ModuleCat.of C (Fin 0 → C)) :=
      ModuleCat.isZero_iff_subsingleton.mpr inferInstance
    have hz :=
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (ComplexShape.up ℤ) q).map_isZero
        (F.map_isZero hzero)
    have : Subsingleton ((F.obj (ModuleCat.of C (Fin 0 → C))).homology q) :=
      ModuleCat.isZero_iff_subsingleton.mp hz
    simp [lam.len_eq_zero_of_subsingleton]
  | succ m ih =>
    let M := ModuleCat.of C C
    let N := ModuleCat.of C (Fin m → C)
    let e := LinearEquiv.piCongrLeft C (fun _ ↦ C) (finSuccEquiv m) ≪≫ₗ
      LinearEquiv.piOptionEquivProd C
    let eh := (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (ComplexShape.up ℤ) q).mapIso
      (F.mapIso e.toModuleIso)
    have hlen : lam.len ((F.obj (ModuleCat.of C (Fin (m + 1) → C))).homology q) =
        lam.len ((F.obj (ModuleCat.of C (C × (Fin m → C)))).homology q) :=
      lam.len_congr _ _ eh.toLinearEquiv
    rw [hlen]
    let S : ShortComplex (ModuleCat.{u} C) :=
      ModuleCat.shortComplexOfCompEqZero (LinearMap.inl C M N) (LinearMap.snd C M N) (by ext; rfl)
    have hS : S.ShortExact := by
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · rw [ShortComplex.moduleCat_exact_iff]
        intro y hy
        exact ⟨y.1, Prod.ext rfl hy.symm⟩
      · exact (ModuleCat.mono_iff_injective _).mpr (fun y z h ↦ congrArg Prod.fst h)
      · exact (ModuleCat.epi_iff_surjective _).mpr (fun y ↦ ⟨(0, y), rfl⟩)
    have := hS.mono_f
    have := hS.epi_g
    have hs := hS.map (HomologicalComplex.single (ModuleCat.{u} C) (ComplexShape.up ℤ) a)
    have hle := lambdaHomology_shortExact_le lam
      ((S.map (HomologicalComplex.single _ _ a)).map (koszulFunctor x))
      (koszulFunctor_shortExact x _ hs) q (ht M) (ht _) (ht N)
    exact hle.trans (by
      change lam.len ((F.obj M).homology q) + lam.len ((F.obj N).homology q) ≤ _
      rw [show lam.len ((F.obj M).homology q) =
        lam.len ((koszulComplex x).homology (q - a)) from
          lambdaHomology_koszul_single_ring_eq lam x a q, succ_nsmul]
      simpa only [add_comm] using add_le_add_left ih (lam.len ((koszulComplex x).homology (q - a))))

/-- 有限自由加群の直和因子に対しても、同じ Koszul 長さの上界が使える。 -/
lemma lambdaHomology_koszul_single_le_of_retract (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical) (a q : ℤ)
    (M : ModuleCat.{u} C) (m : ℕ) (r : Retract M (ModuleCat.of C (Fin m → C))) :
    lam.len ((koszulComplexOn x ((HomologicalComplex.single _ _ a).obj M)).homology q) ≤
      m • lam.len ((koszulComplex x).homology (q - a)) := by
  let P := (HomologicalComplex.single (ModuleCat.{u} C) (ComplexShape.up ℤ) a).obj
    (ModuleCat.of C (Fin m → C))
  have h := lambdaHomology_le_of_retract lam
    ((r.map (HomologicalComplex.single _ _ a)).map (koszulFunctor x)) q
    (supported_homology_isPowTorsion hfg hJ (isSupported_koszulComplexOn x P) q)
  exact h.trans (lambdaHomology_koszul_single_pi_le lam hfg x hJ a q m)

/-- 共通の範囲 `[a, a + w)` にある複体の Koszul ホモロジーの長さを、各項を自由加群の直和因子として表す
自由加群の基底の個数 `r i` と環の Koszul ホモロジーの長さの有限和で抑える。
下端の項への全射の核について帰納するため、任意の短完全列での階数公式は不要。 -/
lemma lambdaHomology_koszulComplexOn_le_sum_of_retracts (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (a : ℤ) (w : ℕ) (r : ℤ → ℕ) (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (hbound : ∀ i, (i < a ∨ a + w ≤ i) → IsZero (P.X i))
    (hterm : ∀ i, a ≤ i → i < a + w → Nonempty (Retract (P.X i) (ModuleCat.of C (Fin (r i) → C))))
    (q : ℤ) :
    lam.len ((koszulComplexOn x P).homology q) ≤
      ∑ j ∈ Finset.range w, r (a + j) • lam.len ((koszulComplex x).homology (q - (a + j))) := by
  induction w generalizing a P with
  | zero =>
    have hz : IsZero P := by
      rw [IsZero.iff_id_eq_zero]
      apply HomologicalComplex.Hom.ext
      funext i
      exact (hbound i (by omega)).eq_of_src _ _
    have hh :=
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (ComplexShape.up ℤ) q).map_isZero
        ((koszulFunctor x).map_isZero hz)
    have : Subsingleton ((koszulComplexOn x P).homology q) :=
      ModuleCat.isZero_iff_subsingleton.mp hh
    simp [lam.len_eq_zero_of_subsingleton]
  | succ w ih =>
    let ha := fun i (hi : i < a) ↦ hbound i (Or.inl hi)
    let π := bottomProjection P a ha
    let P' := kernel π
    have hepi : Epi π := bottomProjection_epi P a ha
    let S : ShortComplex (CochainComplex (ModuleCat.{u} C) ℤ) :=
      ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    have hS : S.ShortExact := { exact := ShortComplex.exact_kernel π }
    have ht (Q : CochainComplex (ModuleCat.{u} C) ℤ) :
        IsPowTorsion J ((koszulComplexOn x Q).homology q) :=
      supported_homology_isPowTorsion hfg hJ (isSupported_koszulComplexOn x Q) q
    have hle := lambdaHomology_shortExact_le lam (S.map (koszulFunctor x))
      (koszulFunctor_shortExact x S hS) q (ht _) (ht _) (ht _)
    have hb' : ∀ i, (i < a + 1 ∨ a + 1 + w ≤ i) → IsZero (P'.X i) := by
      intro i hi
      by_cases hia : i = a
      · subst i
        exact bottomProjection_kernel_isZero P a ha
      · exact (hbound i (by omega)).of_iso (bottomProjectionKernelXIso P a ha i hia)
    have he' : ∀ i, a + 1 ≤ i → i < a + 1 + w →
        Nonempty (Retract (P'.X i) (ModuleCat.of C (Fin (r i) → C))) := by
      intro i hi hi'
      exact ⟨(Retract.ofIso (bottomProjectionKernelXIso P a ha i (by omega))).trans
        (hterm i (by omega) (by omega)).some⟩
    have htail := ih (a + 1) P' hb' he'
    have hhead := lambdaHomology_koszul_single_le_of_retract lam hfg x hJ a q (P.X a) (r a)
      (hterm a le_rfl (by omega)).some
    refine hle.trans ((add_le_add htail hhead).trans_eq ?_)
    rw [Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      have hi : a + 1 + (j : ℤ) = a + (j + 1 : ℕ) := by omega
      rw [hi]
    · have hi : a = a + (0 : ℕ) := by omega
      exact congrArg (fun i : ℤ ↦ r i • lam.len ((koszulComplex x).homology (q - i))) hi

/-- 有限自由項の上界は、各項が有限自由加群の直和因子である場合の特殊例。 -/
lemma lambdaHomology_koszulComplexOn_le_sum (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (a : ℤ) (w : ℕ) (r : ℤ → ℕ) (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (hbound : ∀ i, (i < a ∨ a + w ≤ i) → IsZero (P.X i))
    (hterm : ∀ i, a ≤ i → i < a + w → Nonempty (P.X i ≅ ModuleCat.of C (Fin (r i) → C)))
    (q : ℤ) :
    lam.len ((koszulComplexOn x P).homology q) ≤
      ∑ j ∈ Finset.range w, r (a + j) • lam.len ((koszulComplex x).homology (q - (a + j))) :=
  lambdaHomology_koszulComplexOn_le_sum_of_retracts lam hfg x hJ a w r P hbound
    (fun i hi hi' ↦ ⟨Retract.ofIso (hterm i hi hi').some⟩) q

/-- 各パラメータが零ホモトピックに作用する複体のホモロジーにも、Koszul の
有限和による上界が成り立つ。元の複体を Koszul 複体の直和因子として評価する。 -/
lemma lambdaHomology_le_sum_of_nullHomotopies (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (a : ℤ) (w : ℕ) (r : ℤ → ℕ) (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (hbound : ∀ i, (i < a ∨ a + w ≤ i) → IsZero (P.X i))
    (hterm : ∀ i, a ≤ i → i < a + w → Nonempty (P.X i ≅ ModuleCat.of C (Fin (r i) → C)))
    (hnull : ∀ j, Nonempty (Homotopy (smulId (x j) P) 0)) (q : ℤ) :
    lam.len (P.homology q) ≤
      ∑ j ∈ Finset.range w, r (a + j) • lam.len ((koszulComplex x).homology (q - (a + j))) :=
  (lambdaHomology_le_of_retract lam (retractKoszulComplexOn x P hnull) q
    (supported_homology_isPowTorsion hfg hJ (isSupported_koszulComplexOn x P) q)).trans
    (lambdaHomology_koszulComplexOn_le_sum lam hfg x hJ a w r P hbound hterm q)

end SerrePositivity

end KoszulLengthBoundsPart

section ProjectiveBoundsPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal BigOperators

variable {C : Type u} [CommRing C]

/-- 有限射影加群は有限自由加群の直和因子である。 -/
lemma finiteProjective_exists_retract (M : ModuleCat.{u} C)
    [Module.Finite C M] [Module.Projective C M] :
    ∃ n : ℕ, Nonempty (Retract M (ModuleCat.of C (Fin n → C))) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' C M
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  exact ⟨n, ⟨⟨ModuleCat.ofHom g, ModuleCat.ofHom f, ModuleCat.hom_ext hg⟩⟩⟩

variable {J : Ideal C} (lam : NormalizedLength C J)

/-- 有限射影項の有界複体に対する Koszul ホモロジーの有限性。 -/
lemma lambdaHomology_koszul_projective_ne_top (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (hfin : ∀ q : ℤ, lam.len ((koszulComplex x).homology q) ≠ ⊤)
    (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (hfinite : ∀ q, Module.Finite C (P.X q))
    (hproj : ∀ q, Module.Projective C (P.X q))
    (hbound : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q)) (q : ℤ) :
    lam.len ((koszulComplexOn x P).homology q) ≠ ⊤ := by
  classical
  have hterm (i : ℤ) : ∃ r : ℕ, Nonempty (Retract (P.X i) (ModuleCat.of C (Fin r → C))) := by
    have := hfinite i
    have := hproj i
    exact finiteProjective_exists_retract _
  choose r hr using hterm
  obtain ⟨a, b, hab⟩ := hbound
  have hle := lambdaHomology_koszulComplexOn_le_sum_of_retracts lam hfg x hJ
    a (b + 1 - a).toNat r P (fun i hi ↦ hab i (by omega)) (fun i _ _ ↦ hr i) q
  apply ne_top_of_le_ne_top _ hle
  apply ENNReal.sum_ne_top.mpr
  intro i _
  rw [nsmul_eq_mul]
  exact ENNReal.mul_ne_top (by simp) (hfin _)

/-- Koszul 有限性と台から、有限射影複体の全ホモロジーの長さが有限となる。 -/
theorem lambdaHomology_supported_projective_ne_top (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (hfin : ∀ v : ℕ, 0 < v → ∀ q : ℤ,
      lam.len ((koszulComplex (fun j ↦ x j ^ v)).homology q) ≠ ⊤)
    (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (hfinite : ∀ q, Module.Finite C (P.X q))
    (hproj : ∀ q, Module.Projective C (P.X q))
    (hbound : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (hsupp : IsSupported x P) (q : ℤ) : lam.len (P.homology q) ≠ ⊤ := by
  obtain ⟨v, hv, hnull⟩ := hsupp.exists_pos
  exact lambdaHomology_ne_top_of_koszulComplexOn lam hfg (fun j ↦ x j ^ v)
    (le_radical_span_pow x hJ v) P hnull q
    (lambdaHomology_koszul_projective_ne_top lam hfg (fun j ↦ x j ^ v)
      (le_radical_span_pow x hJ v) (hfin v hv) P hfinite hproj hbound q)

end SerrePositivity

end ProjectiveBoundsPart

section KoszulAmplitudePart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal BigOperators

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)
  (hfg : J.FG) {n : ℕ} (x : Fin n → R)
  (hJ : J ≤ (Ideal.span (Set.range x)).radical)

include hfg hJ in
/-- 有限射影項の振幅と環自身の Koszul 消滅から、係数つき Koszul の振幅を得る。
長さの有限性は仮定しない。 -/
theorem lambdaHomology_koszul_projective_amplitude
    (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf x i) = 0)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfinite : ∀ q, Module.Finite R (P.X q))
    (hproj : ∀ q, Module.Projective R (P.X q))
    (a b : ℤ) (hbound : ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (q : ℤ) (hq : q < a ∨ b < q) :
    lam.len ((koszulComplexOn x P).homology q) = 0 := by
  classical
  have hterm (i : ℤ) : ∃ r : ℕ, Nonempty (Retract (P.X i) (ModuleCat.of R (Fin r → R))) := by
    have := hfinite i
    have := hproj i
    exact finiteProjective_exists_retract _
  choose r hr using hterm
  have hle := lambdaHomology_koszulComplexOn_le_sum_of_retracts lam hfg x hJ
    a (b + 1 - a).toNat r P (fun i hi ↦ hbound i (by omega)) (fun i _ _ ↦ hr i) q
  have hsum : ∑ j ∈ Finset.range ((b + 1 - a).toNat),
      r (a + j) • lam.len ((koszulComplex x).homology (q - (a + j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hz : lam.len ((koszulComplex x).homology (q - (a + j))) = 0 := by
      rcases hq with hq | hq
      · have hn : q - (a + j) = -(((a + j - q).toNat : ℕ) : ℤ) := by omega
        rw [hn]
        exact hzero _ (by omega)
      · have hz := koszulComplex_isZero_homology_of_pos x (q - (a + j)) (by omega)
        have := ModuleCat.subsingleton_of_isZero hz
        exact lam.len_eq_zero_of_subsingleton _
    rw [hz, nsmul_zero]
  exact le_antisymm (hle.trans hsum.le) zero_le

end SerrePositivity

end KoszulAmplitudePart

section MinimalLowerBoundPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 有限個の同じ加群の直積の長さ。無限長の場合も含む。 -/
lemma NormalizedLength.len_fin_fun (M : Type u) [AddCommGroup M] [Module R M]
    (hM : IsPowTorsion J M) (b : ℕ) : lam.len (Fin b → M) = b * lam.len M := by
  have ht (b : ℕ) : IsPowTorsion J (Fin b → M) := by
    obtain ⟨k, hk⟩ := hM
    exact ⟨k, fun m r ↦ funext fun j ↦ hk (x := m j) (a := r)⟩
  induction b with
  | zero => simp [lam.len_eq_zero_of_subsingleton]
  | succ b ih =>
    rw [lam.len_congr _ _ (Fin.consLinearEquiv R (fun _ : Fin (b + 1) ↦ M)).symm,
      TensorRes.len_prod lam M (Fin b → M) hM (ht b), ih, Nat.cast_succ]
    ring

/-- 極小性による Koszul 第零ホモロジーの下界。
元の複体の支持や零ホモトピーは要求しない。 -/
lemma lambdaHomology_koszul_zero_minimal_lower_bound
    (hfg : J.FG) {n : ℕ} (x : Fin n → R)
    (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ q : ℤ, 0 < q → IsZero (P.X q))
    (I : Ideal R) (hI : IsPowTorsion J (R ⧸ I))
    (b : ℕ) (e : P.X 0 ≅ ModuleCat.of R (Fin b → R))
    (hmin : ∀ m : P.X (-1), ∀ j, e.hom.hom ((P.d (-1) 0).hom m) j ∈ I)
    (hx : ∀ j, x j ∈ I) :
    b * lam.len (R ⧸ I) ≤ lam.len ((koszulComplexOn x P).homology 0) := by
  obtain ⟨g, hg⟩ := exists_minimal_koszul_homologyZero_epi P hP I b e hmin x hx
  rw [← lam.len_fin_fun _ hI b]
  exact lam.len_le_of_surjective g.hom ((ModuleCat.epi_iff_surjective _).mp hg)
    (supported_homology_isPowTorsion hfg hJ (isSupported_koszulComplexOn x P) 0)

end SerrePositivity

end MinimalLowerBoundPart
