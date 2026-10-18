module

public import SerrePositivity.KST.DerivedBlowup.ExceptionalTransitionDG

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の例外因子への局所 Koszul 射と遷移の整合性。
方針：Cartier 生成元を追加する包含を外積に延長し、生成元の可換式を dg 関手へ移す。
規約：同一重なり係数環上の局所模型。層の閉埋め込みとの比較は後続工程。
使われ方：例外因子のチャートを blowup のチャートへ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable {B : Type (max u v)} [CommRing B] {I : Type v} [DecidableEq I]

/-- 概要：チャート生成加群の包含は例外因子の関係式と微分を保つ。
方針：pivot 以外の生成元で同じチャート関係式になることを確認する。
規約：KST Lemma 3.6。使われ方：局所 Koszul dg 射を構成する。 -/
theorem exceptionalChartGeneratorInclusion_differential (a x : I → B) (i : I) :
    (Finsupp.linearCombination B (exceptionalRelationValue a x i)).comp
        (exceptionalChartGeneratorInclusion i) = chartKoszulDifferential a x i := by
  apply Finsupp.lhom_ext
  intro j c
  simp [exceptionalChartGeneratorInclusion, chartKoszulDifferential,
    exceptionalRelationValue, j.property]

/-- 概要：blowup チャートから例外因子の局所 dg 代数への指定射。
方針：Cartier 生成元を追加する生成加群の包含を外積 dg 関手にする。
規約：KST Lemma 3.6、スキーム射とは反変の向き。
使われ方：例外因子への制限・pushforward の局所係数射。 -/
def exceptionalChartInclusionDGFunctor (a x : I → B) (i : I) :
    DGFunctor B (ExteriorKoszulObject (chartKoszulDifferential a x i))
      (ExteriorKoszulObject (Finsupp.linearCombination B (exceptionalRelationValue a x i))) :=
  exteriorKoszulDGFunctor (exceptionalChartGeneratorInclusion i)
    (chartKoszulDifferential a x i)
    (Finsupp.linearCombination B (exceptionalRelationValue a x i))
    (exceptionalChartGeneratorInclusion_differential a x i)

/-- 概要：例外因子への局所 dg 射は既存のチャート遷移と可換。
方針：生成加群上の可換式を二つの外積 cochain 合成公式で移す。
規約：KST Def 3.1・Lemma 3.6、規格化座標と可逆推移単元を使用する。
使われ方：例外因子の局所射を重なりに沿って整合させる。 -/
theorem exceptionalChartInclusionDGFunctor_transition (a x : I → B) (i k : I) (s : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) :
    DGFunctor.comp (chartExteriorDGFunctor a x i k s hi hs)
        (exceptionalChartInclusionDGFunctor a x i) =
      (exceptionalChartInclusionDGFunctor a (normalizeCoordinates x s) k).comp
        (exceptionalTransitionDGFunctor a x (normalizeCoordinates x s) i k) := by
  refine EnrichedFunctor.ext (Complex B) (fun _ => rfl) ?_
  intro M N
  simp only [eqToHom_refl, Category.comp_id]
  let f := koszulGeneratorMap i k x s
  let g := exceptionalChartGeneratorInclusion (B := B) i
  let dM := chartKoszulDifferential a (normalizeCoordinates x s) k
  let dN := chartKoszulDifferential a x i
  let dP := Finsupp.linearCombination B (exceptionalRelationValue a x i)
  have hgf : dP.comp (g.comp f) = dM := by
    rw [← LinearMap.comp_assoc, exceptionalChartGeneratorInclusion_differential,
      koszulGeneratorMap_differential a x i k s hi hs]
  let f' := exceptionalChartGeneratorInclusion (B := B) k
  let g' := (exceptionalTransitionEquiv i k x (normalizeCoordinates x s)).toLinearMap
  let dN' := Finsupp.linearCombination B (exceptionalRelationValue a (normalizeCoordinates x s) k)
  have hf' : dN'.comp f' = dM :=
    exceptionalChartGeneratorInclusion_differential a (normalizeCoordinates x s) k
  have hg' : dP.comp g' = dN' :=
    exceptionalTransitionEquiv_differential a x (normalizeCoordinates x s) i k
  have hfg : g'.comp f' = g.comp f := exceptionalTransitionEquiv_chart i k x s hi hs
  change exteriorKoszulCochainMap f dM dN
      (koszulGeneratorMap_differential a x i k s hi hs) ≫
    exteriorKoszulCochainMap g dN dP (exceptionalChartGeneratorInclusion_differential a x i) =
    exteriorKoszulCochainMap (exceptionalChartGeneratorInclusion k) dM
      (Finsupp.linearCombination B (exceptionalRelationValue a (normalizeCoordinates x s) k))
      (exceptionalChartGeneratorInclusion_differential a (normalizeCoordinates x s) k) ≫
    exteriorKoszulCochainMap
      (exceptionalTransitionEquiv i k x (normalizeCoordinates x s)).toLinearMap
      (Finsupp.linearCombination B (exceptionalRelationValue a (normalizeCoordinates x s) k)) dP
      (exceptionalTransitionEquiv_differential a x (normalizeCoordinates x s) i k)
  exact (exteriorKoszulCochainMap_comp f g dM dN dP
    (koszulGeneratorMap_differential a x i k s hi hs)
    (exceptionalChartGeneratorInclusion_differential a x i) hgf).trans
    (exteriorKoszulCochainMap_comp_eq f' g' (g.comp f) dM dN' dP hf' hg' hgf hfg).symm

end SerrePositivity.KST.DerivedBlowup
