module

public import SerrePositivity.KST.DerivedBlowup.FreeKoszulScalarDGFunctor
public import SerrePositivity.KST.DerivedBlowup.RestrictionIdentity

/-!
概要：KST §3.1 の自由 Koszul 模型の連続した dg 係数変更の合成律。
方針：係数制限の合成比較を挿入し、Hom を総外積への単射で比較する。
規約：係数環の合成は環射の合成として扱い、係数制限を明示する。
使われ方：異なる係数環を経由する有限重なりの dg 遷移の整合性。
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

/-- 概要：自由 Koszul の二段の係数変更は合成環射による係数変更に一致する。
方針：dg 関手の外延性と総外積包含の単射性、総外積の係数変更の合成則を使う。
規約：KST §3.1、二段の係数制限を標準 dg 比較で一段にまとめる。
使われ方：全有限チャートの係数変更図式の合成律。 -/
theorem freeKoszulScalarDGFunctor_comp (φ : R →+* S) (ψ : S →+* T) (a : I → R) :
    EnrichedFunctor.comp (Complex R)
      (EnrichedFunctor.comp (Complex R) (freeKoszulScalarDGFunctor φ a)
        (restrictDGFunctor φ (freeKoszulScalarDGFunctor ψ (φ ∘ a))))
      (restrictionCompositionDGFunctor φ ψ
        (ExteriorKoszulObject (Finsupp.linearCombination T (ψ ∘ φ ∘ a)))) =
      freeKoszulScalarDGFunctor (ψ.comp φ) a := by
  refine EnrichedFunctor.ext (Complex R)
    (F := EnrichedFunctor.comp (Complex R)
      (EnrichedFunctor.comp (Complex R) (freeKoszulScalarDGFunctor φ a)
        (restrictDGFunctor φ (freeKoszulScalarDGFunctor ψ (φ ∘ a))))
      (restrictionCompositionDGFunctor φ ψ
        (ExteriorKoszulObject (Finsupp.linearCombination T (ψ ∘ φ ∘ a)))))
    (G := freeKoszulScalarDGFunctor (ψ.comp φ) a) (fun _ => rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply exteriorCochainInclusion_injective (Finsupp.linearCombination T (ψ ∘ φ ∘ a)) q
  change exteriorCochainInclusion (Finsupp.linearCombination T (ψ ∘ φ ∘ a)) q
    (((freeKoszulScalarDGFunctor ψ (φ ∘ a)).map _ _).f q
      (((freeKoszulScalarDGFunctor φ a).map x y).f q z)) =
    exteriorCochainInclusion (Finsupp.linearCombination T ((ψ.comp φ) ∘ a)) q
      (((freeKoszulScalarDGFunctor (ψ.comp φ) a).map x y).f q z)
  rw [freeKoszulScalarDGFunctor_inclusion, freeKoszulScalarDGFunctor_inclusion,
    freeKoszulScalarDGFunctor_inclusion, freeExteriorScalarMap_comp]

/-- 概要：恒等環射による自由 Koszul 係数変更は恒等 dg 関手と一致する。
方針：恒等制限の標準比較で行先を戻し、総外積包含と恒等係数変更公式を使う。
規約：KST §3.1。使われ方：全有限チャートの dg 係数変更の恒等律。 -/
theorem freeKoszulScalarDGFunctor_id (a : I → R) :
    EnrichedFunctor.comp (Complex R) (freeKoszulScalarDGFunctor (RingHom.id R) a)
      (restrictionIdentityDGFunctor R
        (ExteriorKoszulObject (Finsupp.linearCombination R a))) =
      EnrichedFunctor.id (Complex R) (ExteriorKoszulObject (Finsupp.linearCombination R a)) := by
  refine EnrichedFunctor.ext (Complex R)
    (F := EnrichedFunctor.comp (Complex R) (freeKoszulScalarDGFunctor (RingHom.id R) a)
      (restrictionIdentityDGFunctor R
        (ExteriorKoszulObject (Finsupp.linearCombination R a))))
    (G := EnrichedFunctor.id (Complex R)
      (ExteriorKoszulObject (Finsupp.linearCombination R a))) (fun _ => rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply exteriorCochainInclusion_injective (Finsupp.linearCombination R a) q
  change exteriorCochainInclusion (Finsupp.linearCombination R a) q
    (((freeKoszulScalarDGFunctor (RingHom.id R) a).map x y).f q z) =
      exteriorCochainInclusion (Finsupp.linearCombination R a) q z
  exact (freeKoszulScalarDGFunctor_inclusion (RingHom.id R) a x y q z).trans
    (freeExteriorScalarMap_id _)

end SerrePositivity.KST.DerivedBlowup
