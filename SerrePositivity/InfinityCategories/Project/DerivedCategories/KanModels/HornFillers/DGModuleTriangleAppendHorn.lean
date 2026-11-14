module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Triangles.DGModuleTrianglePostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Quasicategory

/-! # 三角形への後合成を表す三次内部ホーン

概要：元の三角形と後合成射を、三つの既知面を持つ内部ホーンへ組み立てる。
方針：厳密な合成三角形二つと元の三角形を貼り、最上位が零の既存充填を使う。
規約：欠けた面の同定は後続。使われ方：β3 の双対比較三単体。
-/
@[expose] public section
open CategoryTheory SerrePositivity.DifferentialGraded

open CochainComplex HomComplex
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {W X Y Z : ModuleCategory A D}
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 二射の厳密合成を零ホモトピーで表す三角形。 -/
def strictDGModuleTriangle (b : X ⟶ Y) (q : Y ⟶ Z) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D b q (b ≫ q) 0 (by simp only [map_zero, sub_self])
/-- 後合成の三次ホーンの各既知面。 -/
def dgModuleTriangleAppendFaces (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : GradedHom A (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y) (-1))
    (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y)).d (-1) 0 t =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val) (q : Y ⟶ Z) :
    ∀ (j : Fin 4) (_ : j ≠ 2), (Δ[2] : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D := fun j _ =>
  ![SSet.yonedaEquiv.symm (strictDGModuleTriangle A D b q).simplex,
    SSet.yonedaEquiv.symm (strictDGModuleTriangle A D c q).simplex,
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.postcomposeDGModuleTriangle A D a b c t ht q),
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D a b c t ht).simplex] j
/-- 三つの既知面は共通の辺で一致する。 -/
lemma dgModuleTriangleAppendFaces_compatible (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : GradedHom A (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y) (-1))
    (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y)).d (-1) 0 t =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val) (q : Y ⟶ Z) :
    SSet.horn.IsCompatible (dgModuleTriangleAppendFaces A D a b c t ht q) := by
  intro j k hj hk hjk
  fin_cases j <;> fin_cases k <;> first
    | exact (hj rfl).elim
    | exact (hk rfl).elim
    | exact False.elim ((show ¬ _ from by decide) hjk)
    | skip
  all_goals symm
  · change SSet.stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm (strictDGModuleTriangle A D c q).simplex =
      SSet.stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm (strictDGModuleTriangle A D b q).simplex
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      (strictDGModuleTriangle A D c q).d₀, (strictDGModuleTriangle A D b q).d₀]
  · change SSet.stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D a b c t ht).simplex =
      SSet.stdSimplex.δ 2 ≫ SSet.yonedaEquiv.symm (strictDGModuleTriangle A D b q).simplex
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D a b c t ht).d₀, (strictDGModuleTriangle A D b q).d₂]
  · change SSet.stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D a b c t ht).simplex =
      SSet.stdSimplex.δ 2 ≫ SSet.yonedaEquiv.symm (strictDGModuleTriangle A D c q).simplex
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D a b c t ht).d₁, (strictDGModuleTriangle A D c q).d₂]
/-- 後合成を表す実際の三次内部ホーン。 -/
def dgModuleTriangleAppendHorn (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : GradedHom A (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y) (-1))
    (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y)).d (-1) 0 t =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val) (q : Y ⟶ Z) :
    (SSet.horn 3 2 : SSet.{max (u + 1) v}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D :=
  Classical.choose (dgModuleTriangleAppendFaces_compatible A D a b c t ht q).exists_desc
/-- ホーン写像の各面は指定した既知面。 -/
lemma dgModuleTriangleAppendHorn_face (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : GradedHom A (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y) (-1))
    (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y)).d (-1) 0 t =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val) (q : Y ⟶ Z)
    (j : Fin 4) (hj : j ≠ 2) :
    SSet.horn.ι 2 j hj ≫ dgModuleTriangleAppendHorn A D a b c t ht q =
      dgModuleTriangleAppendFaces A D a b c t ht q j hj :=
  Classical.choose_spec (dgModuleTriangleAppendFaces_compatible A D a b c t ht q).exists_desc j hj

/-- 三つの既知面を持つ、最上位成分が零の比較三単体。 -/
def dgModuleTriangleAppend (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : GradedHom A (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y) (-1))
    (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y)).d (-1) 0 t =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val) (q : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (RightModule A D) 3 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.filler A (RightModule A D) (dgModuleTriangleAppendHorn A D a b c t ht q)
    (by decide) (by decide)
/-- 比較三単体は各既知面を保つ。 -/
lemma dgModuleTriangleAppend_face (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : GradedHom A (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y) (-1))
    (ht : (moduleHom A D (ForgetEnrichment.to (Complex A) W)
      (ForgetEnrichment.to (Complex A) Y)).d (-1) 0 t =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) c)).val) (q : Y ⟶ Z)
    (j : Fin 4) (hj : j ≠ 2) :
    (dgModuleTriangleAppend A D a b c t ht q).pullback (SimplexCategory.δ j).toOrderHom =
      SSet.yonedaEquiv (dgModuleTriangleAppendFaces A D a b c t ht q j hj) := by
  calc
    _ = (dgModuleTriangleAppendHorn A D a b c t ht q).app _ (SSet.horn.face 2 j hj) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.filler_face A (RightModule A D) _ _ _ j hj
    _ = _ := by
      have hh := congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D))
        (dgModuleTriangleAppendHorn_face A D a b c t ht q j hj)
      rw [SSet.yonedaEquiv_comp] at hh
      exact hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories
