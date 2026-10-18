module

public import SerrePositivity.KST.DerivedBlowup.ChartScalarDGFunctor
public import SerrePositivity.KST.DerivedBlowup.FreeKoszulScalarComposition

/-!
概要：KST §3.1 のチャート dg 係数変更の合成律と恒等律。
方針：微分移送を含めた係数変更の Hom を総外積上で比較する。
規約：二段の係数制限は標準比較で一段にまとめる。
使われ方：全有限重なり環上のチャート dg 図式の関手性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  {I : Type} [DecidableEq I]

/-- 概要：チャートの二段の dg 係数変更は合成環射の係数変更と一致する。
方針：総外積への包含で自由外積の係数変更の合成律に帰着する。
規約：KST §3.1、二段の係数制限比較を明示する。
使われ方：有限重なり環を通る係数変更の合成整合性。 -/
theorem chartScalarDGFunctor_comp (φ : R →+* S) (ψ : S →+* T) (a x : I → R) (i : I) :
    EnrichedFunctor.comp (Complex R)
      (EnrichedFunctor.comp (Complex R) (chartScalarDGFunctor φ a x i)
        (restrictDGFunctor φ (chartScalarDGFunctor ψ (φ ∘ a) (φ ∘ x) i)))
      (restrictionCompositionDGFunctor φ ψ
        (ExteriorKoszulObject (chartKoszulDifferential (ψ ∘ φ ∘ a) (ψ ∘ φ ∘ x) i))) =
      chartScalarDGFunctor (ψ.comp φ) a x i := by
  refine EnrichedFunctor.ext (Complex R)
    (F := EnrichedFunctor.comp (Complex R)
      (EnrichedFunctor.comp (Complex R) (chartScalarDGFunctor φ a x i)
        (restrictDGFunctor φ (chartScalarDGFunctor ψ (φ ∘ a) (φ ∘ x) i)))
      (restrictionCompositionDGFunctor φ ψ
        (ExteriorKoszulObject (chartKoszulDifferential (ψ ∘ φ ∘ a) (ψ ∘ φ ∘ x) i))))
    (G := chartScalarDGFunctor (ψ.comp φ) a x i) (fun _ => rfl) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply exteriorCochainInclusion_injective
    (chartKoszulDifferential (ψ ∘ φ ∘ a) (ψ ∘ φ ∘ x) i) q
  change exteriorCochainInclusion
    (chartKoszulDifferential (ψ ∘ φ ∘ a) (ψ ∘ φ ∘ x) i) q
    (((chartScalarDGFunctor ψ (φ ∘ a) (φ ∘ x) i).map _ _).f q
      (((chartScalarDGFunctor φ a x i).map v w).f q z)) =
    exteriorCochainInclusion
      (chartKoszulDifferential ((ψ.comp φ) ∘ a) ((ψ.comp φ) ∘ x) i) q
      (((chartScalarDGFunctor (ψ.comp φ) a x i).map v w).f q z)
  rw [chartScalarDGFunctor_inclusion, chartScalarDGFunctor_inclusion,
    chartScalarDGFunctor_inclusion, freeExteriorScalarMap_comp]

/-- 概要：恒等環射によるチャートの dg 係数変更は恒等関手と一致する。
方針：総外積への包含で恒等係数変更を計算する。
規約：KST §3.1。使われ方：有限重なりの dg 図式の恒等律。 -/
theorem chartScalarDGFunctor_id (a x : I → R) (i : I) :
    EnrichedFunctor.comp (Complex R) (chartScalarDGFunctor (RingHom.id R) a x i)
      (restrictionIdentityDGFunctor R
        (ExteriorKoszulObject (chartKoszulDifferential a x i))) =
      EnrichedFunctor.id (Complex R) (ExteriorKoszulObject (chartKoszulDifferential a x i)) := by
  refine EnrichedFunctor.ext (Complex R)
    (F := EnrichedFunctor.comp (Complex R) (chartScalarDGFunctor (RingHom.id R) a x i)
      (restrictionIdentityDGFunctor R
        (ExteriorKoszulObject (chartKoszulDifferential a x i))))
    (G := EnrichedFunctor.id (Complex R)
      (ExteriorKoszulObject (chartKoszulDifferential a x i))) (fun _ => rfl) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply exteriorCochainInclusion_injective (chartKoszulDifferential a x i) q
  change exteriorCochainInclusion (chartKoszulDifferential a x i) q
    (((chartScalarDGFunctor (RingHom.id R) a x i).map v w).f q z) =
      exteriorCochainInclusion (chartKoszulDifferential a x i) q z
  exact (chartScalarDGFunctor_inclusion (RingHom.id R) a x i v w q z).trans
    (freeExteriorScalarMap_id _)

end SerrePositivity.KST.DerivedBlowup
