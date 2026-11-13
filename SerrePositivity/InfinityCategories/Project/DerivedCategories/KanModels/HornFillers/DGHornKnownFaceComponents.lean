module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornCanonicalFaces

/-! # 指定面の厳密等式から実ホーンの回収 cochain を比較する

概要：指定面の値が実三角形に等しければ、対応する辺・三角 cochain を型付きに比較できる。
方針：回収データの制限等式と指定面の等式を合成して、既存の異種等号公式を使う。
規約：回収対象族を変えない。使われ方：細分ホーンの残差と実 Q・A の方程式の照合。
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

/-- 指定面の等式から、元の回収辺と同じ実三角形の辺を比較する。 -/
lemma dgLastHornKnownEdge_heq_of_face_eq (j : Fin 4) (hj : j ≠ 3)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2) (ht : σ.app _ (horn.face 3 j hj) = t)
    (a b : Fin 3) (hab : a < b) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (j.succAbove a) (j.succAbove b)
      (j.succAboveOrderEmb.strictMono hab)) (t.edgeHom a b hab) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) t.toSimplexData
    j.succAboveOrderEmb.toOrderHom j.succAboveOrderEmb.injective
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_pullback_face σ j hj).trans (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData ht))
    a b hab (j.succAboveOrderEmb.strictMono hab)

/-- 指定面の等式から、元の回収三角 cochain と同じ実三角形の成分を比較する。 -/
lemma dgLastHornKnownTriangle_heq_of_face_eq (j : Fin 4) (hj : j ≠ 3)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2) (ht : σ.app _ (horn.face 3 j hj) = t) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).tripleHom (j.succAbove 0) (j.succAbove 1) (j.succAbove 2)
      (j.succAboveOrderEmb.strictMono (by decide))
      (j.succAboveOrderEmb.strictMono (by decide))) t.triangleHom := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom_heq_of_pullback_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) t.toSimplexData
    j.succAboveOrderEmb.toOrderHom j.succAboveOrderEmb.injective
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_pullback_face σ j hj).trans (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData ht))
    0 1 2 (by decide) (by decide) (j.succAboveOrderEmb.strictMono (by decide))
    (j.succAboveOrderEmb.strictMono (by decide))
  have he : t.toSimplexData.tripleHom 0 1 2 (by decide) (by decide) = t.triangleHom := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.triangleHom
    congr 1
  exact h.trans (heq_of_eq he)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
