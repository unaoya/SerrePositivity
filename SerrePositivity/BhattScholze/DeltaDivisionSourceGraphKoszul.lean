module

public import SerrePositivity.BhattScholze.DeltaDivisionEvaluationSource
public import SerrePositivity.BhattScholze.DeltaRootFiniteRegularSequence

/-! # 源δ評価核の有限グラフKoszul分解

任意の異なる有限δ座標を扱い、係数環のp正則性・ghost単射・完備性は要求しない。
指数1の商表示は既存APIを用い、正則性はモニック一次式から示す。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

private theorem graph_isSMulRegular {R : Type u} [CommRing R] {τ : Type v}
    (b : τ → R) (s : τ) :
    IsSMulRegular (MvPolynomial τ R) (MvPolynomial.X s - MvPolynomial.C (b s)) := by
  classical
  let e := (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe s).symm).trans
    (MvPolynomial.optionEquivLeft R {t : τ // t ≠ s})
  have he : e (MvPolynomial.X s - MvPolynomial.C (b s)) =
      Polynomial.X - Polynomial.C (MvPolynomial.C (b s)) := by
    simp [e, MvPolynomial.renameEquiv]
  have hr := (Polynomial.monic_X_sub_C (MvPolynomial.C (b s) :
    MvPolynomial {t : τ // t ≠ s} R)).isRegular.left
  intro x y h
  apply e.injective
  apply hr
  have hh := congrArg e h
  simpa only [smul_eq_mul, map_mul, he] using hh

private theorem graph_subset_remaining_regular {R : Type u} [CommRing R] {τ : Type v}
    (T : Set τ) (b : τ → R) (s : τ) (hs : s ∉ T) :
    IsSMulRegular (MvPolynomial τ R ⧸ deltaRootSubsetRelationIdeal (p := 1) T b)
      (Ideal.Quotient.mk (deltaRootSubsetRelationIdeal (p := 1) T b)
        (deltaRootRelationFamily (p := 1) b s)) := by
  let e := deltaRootSubsetQuotientEquiv (p := 1) T b
  have he : e (Ideal.Quotient.mk (deltaRootSubsetRelationIdeal (p := 1) T b)
      (deltaRootRelationFamily (p := 1) b s)) =
      MvPolynomial.X (⟨s, hs⟩ : (Tᶜ : Set τ)) -
        MvPolynomial.C (algebraMap R (MonicPowerFamilyCover 1 T R (fun t => b t)) (b s)) := by
    simp only [deltaRootRelationFamily, pow_one, map_sub, e,
      deltaRootSubsetQuotientEquiv_C]
    rw [deltaRootSubsetQuotientEquiv_X_notMem T b ⟨s, hs⟩]
  have hr := graph_isSMulRegular
    (fun t : (Tᶜ : Set τ) => algebraMap R (MonicPowerFamilyCover 1 T R (fun t => b t)) (b t))
    (⟨s, hs⟩ : (Tᶜ : Set τ))
  intro x y h
  apply e.injective
  apply hr
  have hh := congrArg e h
  simpa only [smul_eq_mul, map_mul, he] using hh

private theorem graph_list_regular {R : Type u} [CommRing R] {τ : Type v}
    (b : τ → R) (l : List τ) (hl : l.Nodup) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial τ R)
      (l.map (deltaRootRelationFamily (p := 1) b)) := by
  constructor
  intro i hi
  have hi' : i < l.length := by simpa only [List.length_map] using hi
  have hs : l[i] ∉ l.take i := by
    intro hm
    obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.mp hm
    rw [List.getElem_take] at hji
    have he := hl.getElem_inj_iff.mp hji
    have hj' : j < i := lt_of_lt_of_le hj (List.length_take_le _ _)
    omega
  have h := graph_subset_remaining_regular {s | s ∈ l.take i} b l[i] hs
  have hr : IsSMulRegular
      (MvPolynomial τ R ⧸ deltaRootSubsetRelationIdeal (p := 1) {s | s ∈ l.take i} b)
      (deltaRootRelationFamily (p := 1) b l[i]) :=
    (isSMulRegular_map (Ideal.Quotient.mk _) (fun _ => rfl)).mp h
  have hI : (Ideal.ofList ((l.map (deltaRootRelationFamily (p := 1) b)).take i) • ⊤ :
      Submodule (MvPolynomial τ R) (MvPolynomial τ R)) =
      deltaRootSubsetRelationIdeal (p := 1) {s | s ∈ l.take i} b := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ← List.map_take, deltaRootRelation_ofList_eq_subset]
  rw [hI, List.getElem_map]
  exact hr

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 源δ評価射の座標グラフ関係。 -/
def deltaDivisionSourceGraphRelation (D : DeltaStructure p A) (a : σ → A) (z : σ × ℕ) :
    RelativeFreeDeltaRing (R := A) σ :=
  MvPolynomial.X z - MvPolynomial.C (D.delta^[z.2] (a z.1))

/-- 任意の異なる有限δ座標の源グラフ関係は弱正則列。 -/
theorem deltaDivisionSourceGraph_fin_isWeaklyRegular (D : DeltaStructure p A) (a : σ → A)
    {m : ℕ} (s : Fin m → σ × ℕ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (RelativeFreeDeltaRing (R := A) σ)
      (List.ofFn fun i => deltaDivisionSourceGraphRelation D a (s i)) := by
  simpa only [List.map_ofFn, Function.comp_def, deltaDivisionSourceGraphRelation,
    deltaRootRelationFamily, pow_one] using
    graph_list_regular (fun z : σ × ℕ => D.delta^[z.2] (a z.1))
      (List.ofFn s) (List.nodup_ofFn_ofInjective hs)

/-- 異なる有限δ座標の源グラフKoszul複体は、その実通常商の分解。 -/
theorem deltaDivisionSourceGraph_fin_isKoszulResolution (D : DeltaStructure p A) (a : σ → A)
    {m : ℕ} (s : Fin m → σ × ℕ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i => deltaDivisionSourceGraphRelation D a (s i)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaDivisionSourceGraph_fin_isWeaklyRegular D a s hs)

/-- 源グラフ関係のαに沿う通常像は、実終域上の評価関係。 -/
theorem deltaDivisionSourceGraph_map (D : DeltaStructure p A) (d : A) (a : σ → A)
    (z : σ × ℕ) :
    deltaDivisionSourceMap D d (deltaDivisionSourceGraphRelation D a z) =
      deltaDivisionEvaluationRelation D d a z.1 z.2 :=
  deltaDivisionSourceMap_graphRelation D d a z.1 z.2

end SerrePositivity.BhattScholze
