module

public import SerrePositivity.KST.DerivedBlowup.FreeExteriorScalarNaturality
public import SerrePositivity.KST.DerivedBlowup.FreeKoszulScalarDGFunctor

/-!
概要：KST §3.1 の自由 Koszul 生成元変換と dg 係数変更の自然性。
方針：微分を保つ二つの生成元変換を総外積への包含で比較する。
規約：行先は係数制限された dg 圏。
使われ方：チャート基底変換と有限重なりの係数制限の整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S]
  {I J : Type} [DecidableEq I] [DecidableEq J]

/-- 概要：生成元上で自然な Koszul 変換は dg 係数変更と可換。
方針：dg 関手の外延性と総外積への包含の単射性で総外積の自然性へ帰着する。
規約：KST §3.1、微分適合性を両係数環で明示する。
使われ方：係数環が変わるチャート dg 遷移の可換図式。 -/
theorem freeKoszulScalarDGFunctor_natural (φ : R →+* S) (a : I → R) (b : J → R)
    (f : (I →₀ R) →ₗ[R] (J →₀ R)) (g : (I →₀ S) →ₗ[S] (J →₀ S))
    (hf : (Finsupp.linearCombination R b).comp f = Finsupp.linearCombination R a)
    (hg : (Finsupp.linearCombination S (φ ∘ b)).comp g =
      Finsupp.linearCombination S (φ ∘ a))
    (h : ∀ m, freeGeneratorScalarMap φ (f m) = g (freeGeneratorScalarMap φ m)) :
    EnrichedFunctor.comp (Complex R)
      (exteriorKoszulDGFunctor f _ _ hf) (freeKoszulScalarDGFunctor φ b) =
    EnrichedFunctor.comp (Complex R) (freeKoszulScalarDGFunctor φ a)
      (restrictDGFunctor φ (exteriorKoszulDGFunctor g _ _ hg)) := by
  refine EnrichedFunctor.ext (Complex R)
    (F := EnrichedFunctor.comp (Complex R)
      (exteriorKoszulDGFunctor f _ _ hf) (freeKoszulScalarDGFunctor φ b))
    (G := EnrichedFunctor.comp (Complex R) (freeKoszulScalarDGFunctor φ a)
      (restrictDGFunctor φ (exteriorKoszulDGFunctor g _ _ hg))) (fun _ => rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply exteriorCochainInclusion_injective (Finsupp.linearCombination S (φ ∘ b)) q
  change exteriorCochainInclusion (Finsupp.linearCombination S (φ ∘ b)) q
      (((freeKoszulScalarDGFunctor φ b).map _ _).f q
        ((exteriorKoszulCochainMap f _ _ hf).f q z)) =
    exteriorCochainInclusion (Finsupp.linearCombination S (φ ∘ b)) q
      ((exteriorKoszulCochainMap g _ _ hg).f q
        (((freeKoszulScalarDGFunctor φ a).map _ _).f q z))
  rw [freeKoszulScalarDGFunctor_inclusion, exteriorCochainInclusion_map,
    exteriorCochainInclusion_map, freeKoszulScalarDGFunctor_inclusion]
  exact freeExteriorScalarMap_natural φ f g h _

end SerrePositivity.KST.DerivedBlowup
