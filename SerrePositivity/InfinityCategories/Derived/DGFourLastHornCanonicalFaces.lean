module
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornCochains

/-! # 四次最後ホーンの回収対象族に固定した指定四面

概要：指定面を、既知データの制限を実データとする三単体として回収する。
方針：面制限の厳密一致で方程式を輸送する。使われ方：高次の共通始域と始点細分。
規約：回収対象族をそのまま用いる。
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

/-- 元の回収データの指定面制限そのものを実三単体として読む。 -/
def dgFourLastHornCanonicalFace (j : Fin 5) (hj : j ≠ 4) : Simplex A D 3 where
  toSimplexData := (HornData.knownData σ).pullback j.succAboveOrderEmb.toOrderHom
  equation := (HornData.knownData_pullback_face σ j hj).symm ▸ (σ.app _ (horn.face 4 j hj)).equation

/-- 回収対象族を使った指定面は、元の実ホーンの面と厳密に同じ。 -/
lemma dgFourLastHornCanonicalFace_eq (j : Fin 5) (hj : j ≠ 4) :
    dgFourLastHornCanonicalFace σ j hj = σ.app _ (horn.face 4 j hj) := by
  apply Simplex.ext
  exact HornData.knownData_pullback_face σ j hj

end SerrePositivity.InfinityCategories
