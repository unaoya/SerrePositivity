module

public import SerrePositivity.AlgebraicGeometry.RelationPivotElimination
public import SerrePositivity.AlgebraicGeometry.PureTransformModule

/-!
概要：KST §5、Stacks 080Z, Lemma 15.8.9 の境界ねじれを除いた後の生成元消去。
方針：境界ねじれに入る擬関係式を、純変換の商で実際の関係式にする。
規約：各元の境界ねじれへの所属を仮定し、一様な消滅指数は要求しない。
使われ方：正則単項の小行列式イデアルから純変換の生成元数を制限する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R P Q M : Type*} [CommRing R] [AddCommGroup P] [AddCommGroup Q]
  [AddCommGroup M] [Module R P] [Module R Q] [Module R M]

/--
概要：可逆な成分を持つ擬関係式の像が境界ねじれなら、純変換は残りの生成元で生成される。
方針：純変換の商写像との合成で擬関係式を零にし、直和成分の消去を使う。
規約：KST §5、Stacks 080Z, Lemma 15.8.9、境界元の正則性は不要。
使われ方：随伴行列が与える境界倍の関係式から純変換の生成元を減らす。
-/
theorem pureTransformPivotComplement_surjective (f : R)
    (q : (P × Q) →ₗ[R] M) (t : P →ₗ[R] (P × Q)) (e : P ≃ₗ[R] P)
    (hq : Function.Surjective q) (ht : ∀ x, q (t x) ∈ boundaryTorsion f M)
    (hfst : (LinearMap.fst R P Q).comp t = e.toLinearMap) :
    Function.Surjective (((boundaryTorsion f M).mkQ.comp q).comp (LinearMap.inr R P Q)) := by
  apply relationPivotComplement_surjective _ t e
  · exact (Submodule.Quotient.mk_surjective (boundaryTorsion f M)).comp hq
  · ext x
    exact (Submodule.Quotient.mk_eq_zero _).mpr (ht x)
  · exact hfst

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
