module

public import SerrePositivity.PerfectComplex.NormalizedEuler
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Koszul ホモロジーの長さの定量評価

## 概要

§4 の列の圏で必要な一様評価を、単一の有限自由複体について証明する。
Lemma 3.5a の有限性の証明を定量化し、各項の基底の個数と、環自身の
Koszul ホモロジーの長さから、係数つき Koszul ホモロジーの長さを抑える。

## 方針と規約

単一複体を基底の個数について帰納し、一般の複体を下端への射の核で分解する。
値は `ℝ≥0∞` のまま扱い、有限性・Noether 性・平坦性は評価の仮定にしない。
基底の個数を明示するので、基底変更後にも元の自由加群の大きさを使える。
次数は cochain 規約で、共通の範囲を `[a, a + w)` と表す。

並行する一般論・§2 の作業と競合しないよう、この段階の補題は独立したファイルに置く。
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped ENNReal BigOperators

namespace SerrePositivity

variable {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)

/-- 短完全列の中央のホモロジーの長さは両端の和以下。
ホモロジーの長完全列と、冪ねじれ加群上の長さの劣加法性を使う。 -/
lemma lambdaHomology_shortExact_le
    (S : ShortComplex (CochainComplex (ModuleCat.{u} C) ℤ)) (hS : S.ShortExact) (q : ℤ)
    (t₁ : IsPowTorsion J (S.X₁.homology q))
    (t₂ : IsPowTorsion J (S.X₂.homology q))
    (t₃ : IsPowTorsion J (S.X₃.homology q)) :
    lam.len (S.X₂.homology q) ≤ lam.len (S.X₁.homology q) + lam.len (S.X₃.homology q) :=
  lam.len_le_add_of_exact (HomologicalComplex.homologyMap S.f q).hom
    (HomologicalComplex.homologyMap S.g q).hom
    (LinearMap.exact_iff.mpr (hS.homology_exact₂ q).moduleCat_range_eq_ker.symm) t₁ t₂ t₃

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
