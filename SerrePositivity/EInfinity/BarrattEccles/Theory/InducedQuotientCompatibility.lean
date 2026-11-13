module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoinvariantQuotientNaturality

/-!
# 誘導表示の単位生成元と指定包含

HA 3.2.4.7 の自由比較の始域側で、誘導表示の逆比較が指定包含を保つことを確認する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory HomologicalComplex

variable {R G : Type u} [CommRing R] [Group G] (H : Subgroup G)
    (V : CochainComplex (Rep.{u} R H) ℤ) (W B : CochainComplex (Rep.{u} R G) ℤ)

/-- 単位生成元を誘導表示の逆比較と指定包含に通すと、元の包含の値を得る。 -/
lemma inducedCoinvariantTotalIso_inv_inclusion
    (ι : V ⟶ ((Rep.resFunctor (k := R) H.subtype).mapHomologicalComplex (.up ℤ)).obj W)
    (i j k : ℤ) (h : i + j = k) (x : V.X i) (y : B.X j) :
    ((inducedCoinvariantTotalIso H.subtype V B).inv ≫
      (inputCoinvariantTotalFunctor B).map (finiteInductionCochainInclusion H V W ι)).f k
      (ιMapBifunctor V (((Rep.resFunctor (k := R) H.subtype).mapHomologicalComplex (.up ℤ)).obj B)
        (Rep.coinvariantsTensor R H) (.up ℤ) i j k h
        (Rep.coinvariantsTensorMk _ _ x y)) =
    ιMapBifunctor W B (Rep.coinvariantsTensor R G) (.up ℤ) i j k h
      (Rep.coinvariantsTensorMk (W.X i) (B.X j) ((ι.f i).hom x) y) := by
  have e := HomologicalComplex₂.ιTotal_map _ _
    (inducedCoinvariantBicomplexIso H.subtype V B).inv (.up ℤ) i j k h
  have e' := congrArg (fun f => f (Rep.coinvariantsTensorMk _ _ x y)) e
  change ((mapBifunctorMap (finiteInductionCochainInclusion H V W ι) (𝟙 B)
    (Rep.coinvariantsTensor R G) (.up ℤ)).f k) _ = _
  change ((mapBifunctorMap (finiteInductionCochainInclusion H V W ι) (𝟙 B)
    (Rep.coinvariantsTensor R G) (.up ℤ)).f k)
    ((HomologicalComplex₂.total.map (inducedCoinvariantBicomplexIso H.subtype V B).inv
      (.up ℤ)).f k _) = _
  simp only at e'
  erw [e']
  have t := congrArg (fun f => f
    ((Rep.coinvariantsTensorIndIso H.subtype (V.X i) (B.X j)).inv
      (Rep.coinvariantsTensorMk _ _ x y)))
    (ι_mapBifunctorMap (finiteInductionCochainInclusion H V W ι) (𝟙 B)
      (Rep.coinvariantsTensor R G) (.up ℤ) i j k h)
  simp only [ModuleCat.comp_apply] at t
  erw [t]
  simp [Rep.coinvariantsTensorIndIso, Rep.coinvariantsTensorIndInv,
    Rep.coinvariantsTensorMk, finiteInductionCochainInclusion, finiteInductionInclusion,
    Rep.indResHomEquiv]

end SerrePositivity.EInfinity
