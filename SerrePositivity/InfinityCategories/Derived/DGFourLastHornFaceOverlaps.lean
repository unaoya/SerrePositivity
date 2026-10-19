module
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornCanonicalFaces
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-! # 実四次最後ホーンの回収指定四面の重なり

概要：回収対象族を使う指定四面は、全ての共有二単体で厳密に一致する。
方針：元の実ホーンの面整合性を米田表示から実単体へ戻す。
規約：対象と全成分の一致。使われ方：同じ閉始点細分後の四面の貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 回収した任意二指定面は、元のホーンの共有面上で厳密に合う。 -/
lemma dgFourLastHornCanonicalFaces_overlap (j k : Fin 5) (hj : j ≠ 4) (hk : k ≠ 4)
    (hjk : j < k) :
    (dgNerve A D).δ (k.pred (Fin.ne_zero_of_lt hjk)) (dgFourLastHornCanonicalFace σ j hj) =
      (dgNerve A D).δ (j.castPred (Fin.ne_last_of_lt hjk))
        (dgFourLastHornCanonicalFace σ k hk) := by
  rw [dgFourLastHornCanonicalFace_eq, dgFourLastHornCanonicalFace_eq]
  have he := congrArg (SSet.yonedaEquiv (X := dgNerve A D))
    ((horn.IsCompatible.of_hom σ).δ_pred_comp j k hj hk hjk)
  rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp] at he
  rw [SSet.yonedaEquiv_comp (horn.ι (4 : Fin 5) j hj) σ,
    SSet.yonedaEquiv_comp (horn.ι (4 : Fin 5) k hk) σ] at he
  exact he

end SerrePositivity.InfinityCategories
