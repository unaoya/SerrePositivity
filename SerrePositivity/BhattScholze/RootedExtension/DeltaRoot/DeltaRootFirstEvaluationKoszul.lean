module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionSourceFiniteTor
public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootAdjoinDivisionVariables

/-! # 一般d根添加の最初の有限評価関係のKoszul分解

根変数と自由δ変数を交換すると、深さ0の関係はモニック根関係の負になる。
正のδ深さ・全源評価環への移行・完備化後の平坦性は含まない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

private theorem neg_list_regular {R : Type u} [CommRing R] (l : List R)
    (h : RingTheory.Sequence.IsWeaklyRegular R l) :
    RingTheory.Sequence.IsWeaklyRegular R (l.map fun x => -x) := by
  have hI (t : List R) : Ideal.ofList (t.map fun x => -x) = Ideal.ofList t := by
    induction t with
    | nil => rfl
    | cons x t ih => simp only [List.map_cons, Ideal.ofList_cons, ih, Ideal.span_singleton_neg]
  constructor
  intro i hi
  have hi' : i < l.length := by simpa only [List.length_map] using hi
  have hr := h.regular_mod_prev i hi'
  rw [← List.map_take, hI, List.getElem_map]
  intro x y hxy
  apply hr
  exact neg_injective (by simpa only [neg_smul] using hxy)

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
/-- 負のモニック根関係の異なる有限族も、任意係数環上で弱正則。 -/
theorem deltaRootRelation_neg_fin_isWeaklyRegular (b : σ → A) {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ A)
      (List.ofFn fun i => -deltaRootRelationFamily (p := p) b (s i)) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    neg_list_regular _ (deltaRootRelation_fin_isWeaklyRegular (p := p) b s hs)

variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b

/-- 変数交換で最初の実評価関係は、移動した係数上のモニック根関係の負になる。 -/
theorem deltaRootFirstEvaluation_swap (s : σ) :
    MvPolynomial.commAlgEquiv A (σ × ℕ) σ
      (deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ s 0) =
      -(deltaRootRelationFamily (p := p)
        (fun t : σ => MvPolynomial.C d * MvPolynomial.X (t, 0) + MvPolynomial.C (b t)) s) := by
  simp only [deltaDivisionEvaluationRelation, Function.iterate_zero_apply,
    deltaRootRelationFamily, map_sub, map_mul, MvPolynomial.commAlgEquiv_C,
    MvPolynomial.commAlgEquiv_X, MvPolynomial.map_C, map_pow, MvPolynomial.map_X,
    MvPolynomial.C_add]
  ring

/-- 任意dに対し、異なる有限個の根の深さ0評価関係は弱正則列。 -/
theorem deltaRootFirstEvaluation_fin_isWeaklyRegular {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (RelativeFreeDeltaRing (R := P₀) σ)
      (List.ofFn fun i => deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ (s i) 0) := by
  let e := MvPolynomial.commAlgEquiv A (σ × ℕ) σ
  let c : σ → MvPolynomial (σ × ℕ) A :=
    fun t => MvPolynomial.C d * MvPolynomial.X (t, 0) + MvPolynomial.C (b t)
  have hr := neg_list_regular _ (deltaRootRelation_fin_isWeaklyRegular (p := p) c s hs)
  have hc := e.toRingEquiv.toAddEquiv.isWeaklyRegular_congr
    (as := List.ofFn fun i => deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ (s i) 0)
    (bs := (List.ofFn fun i =>
      deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ (s i) 0).map e)
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun r _ x => by
        change e (r * x) = e r * e x
        exact map_mul e r x)))
  apply hc.mpr
  simpa only [List.map_ofFn, Function.comp_def, e, deltaRootFirstEvaluation_swap] using hr

/-- 根添加の最初の有限評価Koszul複体は、実通常商の分解。 -/
theorem deltaRootFirstEvaluation_fin_isKoszulResolution {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution
      (fun i => deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ (s i) 0) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaRootFirstEvaluation_fin_isWeaklyRegular D d b s hs)

/-- 一般dの実自由δ射に沿う深さ0有限源グラフ商の正次数Torは零。 -/
theorem deltaRootFirstEvaluation_source_tor_subsingleton {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) (i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg
      (deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)) (i + 1)
      (DeltaDivisionSourceFiniteCoordinateQuotient E₀ c₀ (fun j => (s j, 0)))) := by
  apply deltaDivisionSourceFiniteCoordinate_tor_subsingleton
  · intro j k h
    exact hs (congrArg Prod.fst h)
  · exact deltaRootFirstEvaluation_fin_isKoszulResolution D d b s hs

end SerrePositivity.BhattScholze
