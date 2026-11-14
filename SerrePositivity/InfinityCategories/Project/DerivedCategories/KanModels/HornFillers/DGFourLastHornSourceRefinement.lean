module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGFourLastHornRefinedFaces

/-! # 同じ実閉始点細分後の指定四面を貼った実四次最後ホーン

概要：元の終端面と同じ閉射で細分した三面を、実四次最後外ホーン全体へ貼る。
方針：六つの共有二単体の厳密一致を horn の普遍貼り合わせへ渡す。
規約：充填の存在は主張しない。使われ方：有限同時 Q・A による新しい実ホーンの充填。
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

/-- 同じ閉始点細分後に指定する四つの実三単体の米田表示。 -/
def dgFourLastHornSourceRefinementFace (j : Fin 5) (_hj : j ≠ 4) : Δ[3] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
    (if j = 0 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace0 σ
      else if j = 1 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace1 σ q s
      else if j = 2 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace2 σ q s else _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace3 σ q s)

/-- 同じ閉始点細分後の四面は、六つの共有二単体上で厳密に一致する。 -/
lemma dgFourLastHornSourceRefinement_compatible :
    horn.IsCompatible (dgFourLastHornSourceRefinementFace σ q s) := by
  rw [horn.isCompatible_iff]
  intro i j hi hj hij
  fin_cases i <;> fin_cases j
  all_goals try exact (hi (by decide)).elim
  all_goals try exact (hj (by decide)).elim
  all_goals try exact False.elim ((by decide : ¬ ((0 : Fin 5) < 0)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((1 : Fin 5) < 0)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((1 : Fin 5) < 1)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((2 : Fin 5) < 0)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((2 : Fin 5) < 1)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((2 : Fin 5) < 2)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((3 : Fin 5) < 0)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((3 : Fin 5) < 1)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((3 : Fin 5) < 2)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((3 : Fin 5) < 3)) hij)
  · change SSet.stdSimplex.δ (0 : Fin 4) ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace0 σ) =
      SSet.stdSimplex.δ (0 : Fin 4) ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace1 σ q s)
    apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).injective
    simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFaces_overlap01 σ q s
  · change SSet.stdSimplex.δ (1 : Fin 4) ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace0 σ) =
      SSet.stdSimplex.δ (0 : Fin 4) ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace2 σ q s)
    apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).injective
    simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFaces_overlap02 σ q s
  · change SSet.stdSimplex.δ (2 : Fin 4) ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace0 σ) =
      SSet.stdSimplex.δ (0 : Fin 4) ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace3 σ q s)
    apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).injective
    simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFaces_overlap03 σ q s
  · change SSet.stdSimplex.δ (1 : Fin 4) ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace1 σ q s) =
      SSet.stdSimplex.δ (1 : Fin 4) ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace2 σ q s)
    apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).injective
    simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFaces_overlap12 σ q s
  · change SSet.stdSimplex.δ (2 : Fin 4) ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace1 σ q s) =
      SSet.stdSimplex.δ (1 : Fin 4) ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace3 σ q s)
    apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).injective
    simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFaces_overlap13 σ q s
  · change SSet.stdSimplex.δ (2 : Fin 4) ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace2 σ q s) =
      SSet.stdSimplex.δ (2 : Fin 4) ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace3 σ q s)
    apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).injective
    simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFaces_overlap23 σ q s

/-- 元の指定四面を同じ実閉射で始点細分した、実際の四次最後外ホーン。 -/
def dgFourLastHornSourceRefinement : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  (dgFourLastHornSourceRefinement_compatible σ q s).desc

/-- 細分ホーンの指定面 0 は、元の同じ指定細分面そのもの。 -/
lemma dgFourLastHornSourceRefinement_face0 :
    horn.ι (4 : Fin 5) 0 (by decide) ≫ dgFourLastHornSourceRefinement σ q s =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace0 σ) :=
  (horn.IsCompatible.ι_desc (dgFourLastHornSourceRefinement_compatible σ q s) 0 (by decide)).trans
    (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      (ite_eq_left rfl))

/-- 細分ホーンの指定面 1 は、元の同じ指定細分面そのもの。 -/
lemma dgFourLastHornSourceRefinement_face1 :
    horn.ι (4 : Fin 5) 1 (by decide) ≫ dgFourLastHornSourceRefinement σ q s =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace1 σ q s) :=
  (horn.IsCompatible.ι_desc (dgFourLastHornSourceRefinement_compatible σ q s) 1 (by decide)).trans
    (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      ((ite_eq_right (by decide)).trans (ite_eq_left rfl)))

/-- 細分ホーンの指定面 2 は、元の同じ指定細分面そのもの。 -/
lemma dgFourLastHornSourceRefinement_face2 :
    horn.ι (4 : Fin 5) 2 (by decide) ≫ dgFourLastHornSourceRefinement σ q s =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace2 σ q s) :=
  (horn.IsCompatible.ι_desc (dgFourLastHornSourceRefinement_compatible σ q s) 2 (by decide)).trans
    (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      ((ite_eq_right (by decide)).trans ((ite_eq_right (by decide)).trans (ite_eq_left rfl))))

/-- 細分ホーンの指定面 3 は、元の同じ指定細分面そのもの。 -/
lemma dgFourLastHornSourceRefinement_face3 :
    horn.ι (4 : Fin 5) 3 (by decide) ≫ dgFourLastHornSourceRefinement σ q s =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace3 σ q s) :=
  (horn.IsCompatible.ι_desc (dgFourLastHornSourceRefinement_compatible σ q s) 3 (by decide)).trans
    (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      ((ite_eq_right (by decide)).trans
        ((ite_eq_right (by decide)).trans (ite_eq_right (by decide)))))

/-- 新しい実ホーンの指定終端面は、元のホーンの終端面と厳密に同じ。 -/
lemma dgFourLastHornSourceRefinement_preserves_face0 :
    horn.ι (4 : Fin 5) 0 (by decide) ≫ dgFourLastHornSourceRefinement σ q s =
      horn.ι (4 : Fin 5) 0 (by decide) ≫ σ := by
  rw [dgFourLastHornSourceRefinement_face0]
  apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).injective
  exact ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).apply_symm_apply _).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornCanonicalFace_eq σ 0 (by decide)).trans
      (SSet.yonedaEquiv_comp (horn.ι (4 : Fin 5) 0 (by decide)) σ).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
