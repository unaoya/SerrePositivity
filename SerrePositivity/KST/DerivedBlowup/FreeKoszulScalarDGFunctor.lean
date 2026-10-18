module

public import SerrePositivity.KST.DerivedBlowup.FreeExteriorScalarMap
public import SerrePositivity.KST.DerivedBlowup.RestrictionComposition

/-!
概要：KST §3.1 の自由 Koszul 模型の環射に沿う dg 関手を構成する。
方針：係数変更の単位と底変更比較を合成し、総外積への包含で Hom の像を計算する。
規約：行先は係数制限された dg 圏であり、元の係数環上で比較する。
使われ方：異なる係数環を通るチャート遷移の合成則。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension
open scoped TensorProduct

variable {R S : Type u} [CommRing R] [CommRing S] {I : Type} [DecidableEq I]

/-- 概要：環射に沿う自由 Koszul 模型の dg 関手。
方針：随伴単位の後に自由生成加群の底変更同型を適用する。
規約：KST §3.1。使われ方：チャートの係数変更と遷移の比較。 -/
def freeKoszulScalarDGFunctor (φ : R →+* S) (a : I → R) :
    DGFunctor R (ExteriorKoszulObject (Finsupp.linearCombination R a))
      (DGRestriction φ (ExteriorKoszulObject (Finsupp.linearCombination S (φ ∘ a)))) := by
  letI := φ.toAlgebra
  exact EnrichedFunctor.comp (Complex R)
    (unitDGFunctor φ (ExteriorKoszulObject (Finsupp.linearCombination R a)))
    (restrictDGFunctor φ (freeKoszulBaseChangeDGFunctor φ a))

/-- 概要：自由 Koszul 係数変更の Hom の像は総外積の係数変更と一致する。
方針：底変更複体同型と生成加群変換の包含公式を順に使う。
規約：KST §3.1。使われ方：連続した dg 係数変更の合成比較。 -/
theorem freeKoszulScalarDGFunctor_inclusion (φ : R →+* S) (a : I → R)
    (x y : ExteriorKoszulObject (Finsupp.linearCombination R a)) (q : ℤ)
    (z : (exteriorKoszulCochain (Finsupp.linearCombination R a)).X q) :
    exteriorCochainInclusion (Finsupp.linearCombination S (φ ∘ a)) q
        (((freeKoszulScalarDGFunctor φ a).map x y).f q z) =
      freeExteriorScalarMap φ
        (exteriorCochainInclusion (Finsupp.linearCombination R a) q z) := by
  let := φ.toAlgebra
  change exteriorCochainInclusion (Finsupp.linearCombination S (φ ∘ a)) q
    ((exteriorKoszulCochainMap (freeKoszulBaseChangeGeneratorEquiv φ I).toLinearMap
      (exteriorBaseChangeDifferential (S := S) (Finsupp.linearCombination R a))
      (Finsupp.linearCombination S (φ ∘ a))
      (freeKoszulBaseChangeGeneratorEquiv_differential φ a)).f q
      ((exteriorCochainBaseChangeIso φ (Finsupp.linearCombination R a)).inv.f q
        ((1 : S) ⊗ₜ[R] z))) = _
  rw [exteriorCochainInclusion_map, exteriorBaseChangeCochainInclusion_iso_inv]
  change ExteriorAlgebra.map (freeKoszulBaseChangeGeneratorEquiv φ I).toLinearMap
    (exteriorOfBaseChange ((1 : S) ⊗ₜ[R]
      exteriorCochainInclusion (Finsupp.linearCombination R a) q z)) = _
  change ExteriorAlgebra.map (freeKoszulBaseChangeGeneratorEquiv φ I).toLinearMap
    (algebraMap S _ 1 * exteriorOfBaseChangeAux
      (exteriorCochainInclusion (Finsupp.linearCombination R a) q z)) = _
  rw [map_one, one_mul]
  rfl

end SerrePositivity.KST.DerivedBlowup
