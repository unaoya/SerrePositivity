module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornFaceDifferentials

/-! # 最後外ホーンの回収データを持つ実指定三面

概要：各指定面を、元の回収対象族の制限を厳密な対象族とする実二単体として読む。
方針：既知データの面制限等式で全方程式を移し、元の指定面との等式を保つ。
規約：対象族を回収データへ固定する。使われ方：同じ閉射を二つの始点へ細分する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 回収データの面制限を実データとする、元の指定面そのものの二単体。 -/
def dgLastHornCanonicalFace (j : Fin 4) (hj : j ≠ 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2 where
  toSimplexData := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).pullback j.succAboveOrderEmb.toOrderHom
  equation := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_pullback_face σ j hj).symm ▸ (σ.app _ (horn.face 3 j hj)).equation

/-- 回収対象族を使った指定面は、元の実ホーンの指定二単体と厳密に同じ。 -/
lemma dgLastHornCanonicalFace_eq (j : Fin 4) (hj : j ≠ 3) :
    dgLastHornCanonicalFace σ j hj = σ.app _ (horn.face 3 j hj) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_pullback_face σ j hj

/-- 指定面の任意の辺は、回収した対応する元の辺そのもの。 -/
lemma dgLastHornCanonicalFace_edge (j : Fin 4) (hj : j ≠ 3)
    (a b : Fin 3) (hab : a < b) :
    (dgLastHornCanonicalFace σ j hj).edgeHom a b hab =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (j.succAbove a) (j.succAbove b)
        (j.succAboveOrderEmb.strictMono hab) :=
  (eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ)
    (dgLastHornCanonicalFace σ j hj).toSimplexData j.succAboveOrderEmb.toOrderHom
    j.succAboveOrderEmb.injective rfl a b hab (j.succAboveOrderEmb.strictMono hab))).symm

/-- 指定面の三角 cochain は、回収した対応する三点成分そのもの。 -/
lemma dgLastHornCanonicalFace_triangle (j : Fin 4) (hj : j ≠ 3) :
    (dgLastHornCanonicalFace σ j hj).triangleHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).tripleHom (j.succAbove 0) (j.succAbove 1) (j.succAbove 2)
        (j.succAboveOrderEmb.strictMono (by decide))
        (j.succAboveOrderEmb.strictMono (by decide)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom_heq_of_pullback_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ)
    (dgLastHornCanonicalFace σ j hj).toSimplexData j.succAboveOrderEmb.toOrderHom
    j.succAboveOrderEmb.injective rfl 0 1 2 (by decide) (by decide)
    (j.succAboveOrderEmb.strictMono (by decide)) (j.succAboveOrderEmb.strictMono (by decide))
  have he : (dgLastHornCanonicalFace σ j hj).toSimplexData.tripleHom 0 1 2
      (by decide) (by decide) = (dgLastHornCanonicalFace σ j hj).triangleHom := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.triangleHom
    congr 1
  exact he.symm.trans (eq_of_heq h).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
