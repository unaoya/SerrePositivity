module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornRefinedFaces

/-! # 同じ実閉細分後の指定三面を貼った実最後外ホーン

概要：元の終端面と同じ閉射で細分した二面を、実三次最後外ホーン全体へ貼る。
方針：三共通辺の厳密一致を horn の普遍貼り合わせへ渡す。
規約：欠けた面の存在は要求しない。使われ方：回収済み Q・A による新ホーンの充填。
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
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))

/-- 閉始点細分後に指定する三つの実面の米田表示。 -/
def dgLastHornSourceRefinementFace (j : Fin 4) (_hj : j ≠ 3) : Δ[2] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
    (if j = 0 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace0 σ
      else if j = 1 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace1 σ q s else _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace2 σ q s)

/-- 同じ実閉細分後の指定三面は、三つの共通辺上で厳密に一致する。 -/
lemma dgLastHornSourceRefinement_compatible :
    horn.IsCompatible (dgLastHornSourceRefinementFace σ q s) := by
  rw [horn.isCompatible_iff]
  intro i j hi hj hij
  fin_cases i <;> fin_cases j
  all_goals try exact (hi (by decide)).elim
  all_goals try exact (hj (by decide)).elim
  all_goals try exact False.elim ((by decide : ¬ ((0 : Fin 4) < 0)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((1 : Fin 4) < 0)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((1 : Fin 4) < 1)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((2 : Fin 4) < 0)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((2 : Fin 4) < 1)) hij)
  all_goals try exact False.elim ((by decide : ¬ ((2 : Fin 4) < 2)) hij)
  · change SSet.stdSimplex.δ (0 : Fin 3) ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace0 σ) =
      SSet.stdSimplex.δ (0 : Fin 3) ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace1 σ q s)
    apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).injective
    simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFaces_overlap01 σ q s
  · change SSet.stdSimplex.δ (1 : Fin 3) ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace0 σ) =
      SSet.stdSimplex.δ (0 : Fin 3) ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace2 σ q s)
    apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).injective
    simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFaces_overlap02 σ q s
  · change SSet.stdSimplex.δ (1 : Fin 3) ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace1 σ q s) =
      SSet.stdSimplex.δ (1 : Fin 3) ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace2 σ q s)
    apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).injective
    simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFaces_overlap12 σ q s

/-- 元の指定三面を同じ実閉射で始点細分した、実際の三次最後外ホーン。 -/
def dgLastHornSourceRefinement : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  (dgLastHornSourceRefinement_compatible σ q s).desc

/-- 細分した零面は、元の指定終端面を保つ。 -/
lemma dgLastHornSourceRefinement_face0 :
    horn.ι (3 : Fin 4) 0 (by decide) ≫ dgLastHornSourceRefinement σ q s =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace0 σ) :=
  (horn.IsCompatible.ι_desc (dgLastHornSourceRefinement_compatible σ q s) 0 (by decide)).trans
    (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (ite_eq_left rfl))

/-- 細分した一面は、元の面 023 の同じ閉細分そのもの。 -/
lemma dgLastHornSourceRefinement_face1 :
    horn.ι (3 : Fin 4) 1 (by decide) ≫ dgLastHornSourceRefinement σ q s =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace1 σ q s) :=
  (horn.IsCompatible.ι_desc (dgLastHornSourceRefinement_compatible σ q s) 1 (by decide)).trans
    (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      ((ite_eq_right (by decide)).trans (ite_eq_left rfl)))

/-- 細分した二面は、元の面 013 の同じ閉細分そのもの。 -/
lemma dgLastHornSourceRefinement_face2 :
    horn.ι (3 : Fin 4) 2 (by decide) ≫ dgLastHornSourceRefinement σ q s =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornRefinedFace2 σ q s) :=
  (horn.IsCompatible.ι_desc (dgLastHornSourceRefinement_compatible σ q s) 2 (by decide)).trans
    (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      ((ite_eq_right (by decide)).trans (ite_eq_right (by decide))))

/-- 新ホーンの指定終端面は、元の実ホーンの指定終端面と厳密に一致する。 -/
lemma dgLastHornSourceRefinement_preserves_face0 :
    horn.ι (3 : Fin 4) 0 (by decide) ≫ dgLastHornSourceRefinement σ q s =
      horn.ι (3 : Fin 4) 0 (by decide) ≫ σ := by
  rw [dgLastHornSourceRefinement_face0]
  apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).injective
  exact ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).apply_symm_apply _).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace_eq σ 0 (by decide)).trans
      (SSet.yonedaEquiv_comp (horn.ι (3 : Fin 4) 0 (by decide)) σ).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
