module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGModuleTriangleAppendHorn

/-! # 三角形の中間対象の因子分解比較

概要：a と m と b に沿う因子分解を、三つの既知面を持つ内部三次ホーンへ組み立てる。
方針：二つの厳密三角形と、同じ対角・ホモトピーを持つ対象変更後の三角形を貼る。
規約：欠けた面は 2。使われ方：D7 の cofiber から suspension への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
variable {W X Y Z : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
variable (a : W ⟶ X) (m : X ⟶ Y) (b : Y ⟶ Z) (c : W ⟶ Z)
variable (t : _root_.SerrePositivity.DifferentialGraded.GradedHom R (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) W)
  (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) Z) (-1))
variable (ht : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) W)
  (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) Z)).d (-1) 0 t =
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R) ((a ≫ m) ≫ b))).val -
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R) c)).val)

/-- 因子分解比較の三つの指定面。 -/
def dgModuleTriangleMiddleFaces :
    ∀ (j : Fin 4) (_ : j ≠ 2), (Δ[2] : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D := fun j _ =>
  ![SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictDGModuleTriangle R D m b).simplex,
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct R D (a ≫ m) b c t ht).simplex,
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictDGModuleTriangle R D m b).simplex,
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictDGModuleTriangle R D a m).simplex] j

/-- 指定した三角形は共通の辺で一致する。 -/
lemma dgModuleTriangleMiddleFaces_compatible :
    SSet.horn.IsCompatible (dgModuleTriangleMiddleFaces R D a m b c t ht) := by
  intro j k hj hk hjk
  fin_cases j <;> fin_cases k <;> first
    | exact (hj rfl).elim
    | exact (hk rfl).elim
    | exact False.elim ((show ¬ _ from by decide) hjk)
    | skip
  all_goals symm
  · change SSet.stdSimplex.δ 0 ≫
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct R D (a ≫ m) b c t ht).simplex =
      SSet.stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictDGModuleTriangle R D m b).simplex
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct R D (a ≫ m) b c t ht).d₀, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictDGModuleTriangle R D m b).d₀]
  · change SSet.stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictDGModuleTriangle R D a m).simplex =
      SSet.stdSimplex.δ 2 ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictDGModuleTriangle R D m b).simplex
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictDGModuleTriangle R D a m).d₀, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictDGModuleTriangle R D m b).d₂]
  · change SSet.stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictDGModuleTriangle R D a m).simplex =
      SSet.stdSimplex.δ 2 ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct R D (a ≫ m) b c t ht).simplex
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictDGModuleTriangle R D a m).d₁, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct R D (a ≫ m) b c t ht).d₂]

/-- 中間対象の因子分解比較の実際の内部ホーン。 -/
def dgModuleTriangleMiddleHorn : (SSet.horn 3 2 : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D :=
  Classical.choose (dgModuleTriangleMiddleFaces_compatible R D a m b c t ht).exists_desc

/-- 内部ホーンは指定面を保つ。 -/
lemma dgModuleTriangleMiddleHorn_face (j : Fin 4) (hj : j ≠ 2) :
    SSet.horn.ι 2 j hj ≫ dgModuleTriangleMiddleHorn R D a m b c t ht =
      dgModuleTriangleMiddleFaces R D a m b c t ht j hj :=
  Classical.choose_spec (dgModuleTriangleMiddleFaces_compatible R D a m b c t ht).exists_desc j hj

/-- 最上位成分が零の中間対象比較三単体。 -/
def dgModuleTriangleMiddle : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (RightModule R D) 3 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.filler R (RightModule R D) (dgModuleTriangleMiddleHorn R D a m b c t ht)
    (by decide) (by decide)

/-- 三単体は三つの指定面を保つ。 -/
lemma dgModuleTriangleMiddle_face (j : Fin 4) (hj : j ≠ 2) :
    (dgModuleTriangleMiddle R D a m b c t ht).pullback (SimplexCategory.δ j).toOrderHom =
      SSet.yonedaEquiv (dgModuleTriangleMiddleFaces R D a m b c t ht j hj) := by
  calc
    _ = (dgModuleTriangleMiddleHorn R D a m b c t ht).app _ (SSet.horn.face 2 j hj) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.filler_face R (RightModule R D) _ _ _ j hj
    _ = _ := by
      have hh := congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R D))
        (dgModuleTriangleMiddleHorn_face R D a m b c t ht j hj)
      rw [SSet.yonedaEquiv_comp] at hh
      exact hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories
