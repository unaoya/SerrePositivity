module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGFourLastHornSourceRefinement

/-! # 閉始点細分した実ホーンの指定面の値と回収対象

概要：貼った実ホーンの全指定二単体と五つの回収対象を厳密に同定する。
方針：米田表示の貼り合わせ等式を実単体へ戻し、既知面から頂点を回収する。
規約：新しい始点は指定 q、他の四対象は元の回収対象。使われ方：Q・A の型付き輸送。
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
variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))

/-- 貼ったホーンの零面の実三単体は、元の指定終端面。 -/
lemma dgFourLastHornSourceRefinement_value0 :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s).app _ (horn.face 4 0 (by decide)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace0 σ :=
  (SSet.yonedaEquiv_comp (horn.ι (4 : Fin 5) 0 (by decide))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s)).symm.trans
      ((congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_face0 σ q s)).trans
          ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).apply_symm_apply _))

/-- 貼ったホーンの一面の実三単体は、元の面 0234 の同じ閉細分。 -/
lemma dgFourLastHornSourceRefinement_value1 :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s).app _ (horn.face 4 1 (by decide)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace1 σ q s :=
  (SSet.yonedaEquiv_comp (horn.ι (4 : Fin 5) 1 (by decide))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s)).symm.trans
      ((congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_face1 σ q s)).trans
          ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).apply_symm_apply _))

/-- 貼ったホーンの二面の実三単体は、元の面 0134 の同じ閉細分。 -/
lemma dgFourLastHornSourceRefinement_value2 :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s).app _ (horn.face 4 2 (by decide)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace2 σ q s :=
  (SSet.yonedaEquiv_comp (horn.ι (4 : Fin 5) 2 (by decide))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s)).symm.trans
      ((congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_face2 σ q s)).trans
          ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).apply_symm_apply _))

/-- 貼った四次ホーンの三面の実三単体は、元の面 0124 の同じ閉細分。 -/
lemma dgFourLastHornSourceRefinement_value3 :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s).app _ (horn.face 4 3 (by decide)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace3 σ q s :=
  (SSet.yonedaEquiv_comp (horn.ι (4 : Fin 5) 3 (by decide))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s)).symm.trans
      ((congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_face3 σ q s)).trans
          ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).apply_symm_apply _))

/-- 新ホーンの回収始点は、指定した追加閉細分の始対象 q。 -/
lemma dgFourLastHornSourceRefinement_obj0 :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s)).obj 0 = q :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.face_obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s) 1 (by decide) 0).symm.trans
    (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 3 => t.obj 0) (dgFourLastHornSourceRefinement_value1 σ q s))

/-- 新ホーンの回収対象 1 は元の対象 1。 -/
lemma dgFourLastHornSourceRefinement_obj1 :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s)).obj 1 =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 1 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.face_obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s) 0 (by decide) 0).symm.trans
    (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 3 => t.obj 0) (dgFourLastHornSourceRefinement_value0 σ q s))

/-- 新ホーンの回収対象 2 は元の対象 2。 -/
lemma dgFourLastHornSourceRefinement_obj2 :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s)).obj 2 =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 2 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.face_obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s) 0 (by decide) 1).symm.trans
    (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 3 => t.obj 1) (dgFourLastHornSourceRefinement_value0 σ q s))

/-- 新ホーンの回収対象 3 は元の対象 3。 -/
lemma dgFourLastHornSourceRefinement_obj3 :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s)).obj 3 =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.face_obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s) 0 (by decide) 2).symm.trans
    (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 3 => t.obj 2) (dgFourLastHornSourceRefinement_value0 σ q s))

/-- 新四次ホーンの回収対象 4 は元の指定終点。 -/
lemma dgFourLastHornSourceRefinement_obj4 :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s)).obj 4 =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 4 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.face_obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s) 0 (by decide) 3).symm.trans
    (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 3 => t.obj 3) (dgFourLastHornSourceRefinement_value0 σ q s))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
