module

public import SerrePositivity.KST.DerivedBlowup.ExceptionalSemilinearTransition
public import SerrePositivity.KST.DerivedBlowup.ChartSemilinearTransition

/-!
概要：KST v4 Def 3.1・Lemma 3.6（pp.11–14）の係数環を変える局所例外因子射の整合性。
方針：両経路を総外積へ包含し、包含の係数自然性と重なり基底変換の可換式を使う。
規約：元座標が目標の規格化座標へ移る条件を明示する。
使われ方：実際の有限重なり環射に沿う例外因子の局所 dg 射の可換四角形。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded DifferentialGraded.ScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S] {I : Type} [DecidableEq I]

set_option maxHeartbeats 2000000 in
-- 二つの係数環の Hom と三段の係数制限の成分を照合するために必要。
/-- 概要：半線形チャート遷移と例外因子への局所 dg 係数射は可換。
方針：指定 Hom 写像の総外積上の公式を使い、生成加群の可換式へ帰着する。
規約：KST Def 3.1・Lemma 3.6、係数と座標の移送を省略しない。
使われ方：例外因子の局所射を有限重なり図式にまとめる。 -/
theorem exceptionalSemilinearDGFunctor_chart_square
    (φ : R →+* S) (a x : I → R) (b y : I → S) (i k : I) (s : Sˣ)
    (ha : φ ∘ a = b) (hx : φ ∘ x = normalizeCoordinates y s)
    (hk : y k = 1) (hs : ↑s = y i) :
    EnrichedFunctor.comp (Complex R) (chartSemilinearDGFunctor φ a x b y i k s ha hx hk hs)
        (restrictDGFunctor φ (exceptionalChartInclusionDGFunctor b y k)) =
      EnrichedFunctor.comp (Complex R) (exceptionalChartInclusionDGFunctor a x i)
        (exceptionalSemilinearDGFunctor φ a x b y i k ha) := by
  refine EnrichedFunctor.ext (Complex R)
    (F := EnrichedFunctor.comp (Complex R) (chartSemilinearDGFunctor φ a x b y i k s ha hx hk hs)
      (restrictDGFunctor φ (exceptionalChartInclusionDGFunctor b y k)))
    (G := EnrichedFunctor.comp (Complex R) (exceptionalChartInclusionDGFunctor a x i)
      (exceptionalSemilinearDGFunctor φ a x b y i k ha)) (fun _ => rfl) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply exteriorCochainInclusion_injective
    (Finsupp.linearCombination S (exceptionalRelationValue b y k)) q
  change exteriorCochainInclusion
      (Finsupp.linearCombination S (exceptionalRelationValue b y k)) q
      ((exteriorKoszulCochainMap (exceptionalChartGeneratorInclusion k) _ _ _).f q
        (((chartSemilinearDGFunctor φ a x b y i k s ha hx hk hs).map v w).f q z)) =
    exteriorCochainInclusion
      (Finsupp.linearCombination S (exceptionalRelationValue b y k)) q
      (((exceptionalSemilinearDGFunctor φ a x b y i k ha).map _ _).f q
        ((exteriorKoszulCochainMap (exceptionalChartGeneratorInclusion i) _ _ _).f q z))
  rw [exteriorCochainInclusion_map, chartSemilinearDGFunctor_inclusion,
    exceptionalSemilinearDGFunctor_inclusion, exteriorCochainInclusion_map]
  rw [freeExteriorScalarMap_natural φ (exceptionalChartGeneratorInclusion i)
    (exceptionalChartGeneratorInclusion i) (exceptionalChartGeneratorInclusion_scalarMap φ i)]
  rw [hx, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  exact congrArg (fun f => ExteriorAlgebra.map f
    (freeExteriorScalarMap φ (exteriorCochainInclusion (chartKoszulDifferential a x i) q z)))
      (exceptionalTransitionEquiv_chart k i y s hk hs).symm

end SerrePositivity.KST.DerivedBlowup
