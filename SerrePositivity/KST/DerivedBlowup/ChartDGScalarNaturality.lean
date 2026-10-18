module

public import SerrePositivity.KST.DerivedBlowup.ChartScalarNormalization

/-!
概要：KST §3.1 のチャート基底変換と dg 係数変更の自然性。
方針：微分移送を行先に含めた係数変更を使い、総外積への単射で二経路を比較する。
規約：規格化と係数変更の順序の違いも明示的な dg 関手で吸収する。
使われ方：全有限重なりでの異なる係数環を通る dg 遷移の合成整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S] {I : Type} [DecidableEq I]

/-- 概要：チャート基底変換は dg 係数変更と可換。
方針：両経路の Hom を総外積へ包含し、基底変換行列の係数自然性を適用する。
規約：KST §3.1、行先の規格化座標の移送を標準比較に含める。
使われ方：係数環が変わるチャート dg 図式の可換四角形。 -/
theorem chartExteriorDGFunctor_scalar_natural (φ : R →+* S) (a x : I → R)
    (i k : I) (s : Rˣ) (hi : x i = 1) (hs : ↑s = x k) :
    EnrichedFunctor.comp (Complex R) (chartExteriorDGFunctor a x i k s hi hs)
      (chartScalarDGFunctor φ a x i) =
    EnrichedFunctor.comp (Complex R) (chartScalarNormalizedDGFunctor φ a x k s)
      (restrictDGFunctor φ (chartExteriorDGFunctor (φ ∘ a) (φ ∘ x) i k
        (Units.map φ.toMonoidHom s) (by change φ (x i) = 1; rw [hi, map_one])
        (by change φ (↑s) = φ (x k); rw [hs]))) := by
  refine EnrichedFunctor.ext (Complex R)
    (F := EnrichedFunctor.comp (Complex R) (chartExteriorDGFunctor a x i k s hi hs)
      (chartScalarDGFunctor φ a x i))
    (G := EnrichedFunctor.comp (Complex R) (chartScalarNormalizedDGFunctor φ a x k s)
      (restrictDGFunctor φ (chartExteriorDGFunctor (φ ∘ a) (φ ∘ x) i k
        (Units.map φ.toMonoidHom s) (by change φ (x i) = 1; rw [hi, map_one])
        (by change φ (↑s) = φ (x k); rw [hs])))) (fun _ => rfl) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply exteriorCochainInclusion_injective (chartKoszulDifferential (φ ∘ a) (φ ∘ x) i) q
  change exteriorCochainInclusion (chartKoszulDifferential (φ ∘ a) (φ ∘ x) i) q
    (((chartScalarDGFunctor φ a x i).map _ _).f q
      ((exteriorKoszulCochainMap (koszulGeneratorMap i k x s) _ _ _).f q z)) =
    exteriorCochainInclusion (chartKoszulDifferential (φ ∘ a) (φ ∘ x) i) q
      ((exteriorKoszulCochainMap
        (koszulGeneratorMap i k (φ ∘ x) (Units.map φ.toMonoidHom s)) _ _ _).f q
        (((chartScalarNormalizedDGFunctor φ a x k s).map v w).f q z))
  rw [chartScalarDGFunctor_inclusion, exteriorCochainInclusion_map,
    exteriorCochainInclusion_map, chartScalarNormalizedDGFunctor_inclusion]
  exact freeExteriorScalarMap_natural φ (koszulGeneratorMap i k x s)
    (koszulGeneratorMap i k (φ ∘ x) (Units.map φ.toMonoidHom s))
    (koszulGeneratorMap_scalarMap φ i k x s) _

end SerrePositivity.KST.DerivedBlowup
