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
    deltaRootRelation_list_isWeaklyRegular_of_ne_zero (p := 1) one_ne_zero
      (fun z : σ × ℕ => D.delta^[z.2] (a z.1))
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
