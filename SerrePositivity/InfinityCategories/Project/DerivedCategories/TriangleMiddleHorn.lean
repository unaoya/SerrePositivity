module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TriangleAppendHorn

/-! # 三角形の中間対象の因子分解比較

概要：a と m と b に沿う因子分解を、三つの既知面を持つ内部三次ホーンへ組み立てる。
方針：二つの厳密三角形と、同じ対角・ホモトピーを持つ対象変更後の三角形を貼る。
規約：欠けた面は 2。使われ方：D7 の cofiber から suspension への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C D : _root_.SerrePositivity.DifferentialGraded.Complex S}
variable (a : A ⟶ B) (m : B ⟶ C) (b : C ⟶ D) (c : A ⟶ D) (t : Cochain A D (-1))
variable (ht : δ (-1) 0 t = Cochain.ofHom ((a ≫ m) ≫ b) - Cochain.ofHom c)

/-- 因子分解比較の三つの指定面。 -/
def complexTriangleMiddleFaces :
    ∀ (j : Fin 4) (_ : j ≠ 2), (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S) := fun j _ =>
  ![SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictComplexTriangle m b).simplex,
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct (a ≫ m) b c t ht).simplex,
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictComplexTriangle m b).simplex,
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictComplexTriangle a m).simplex] j

/-- 指定した三角形は共通の辺で一致する。 -/
lemma complexTriangleMiddleFaces_compatible :
    SSet.horn.IsCompatible (complexTriangleMiddleFaces a m b c t ht) := by
  intro j k hj hk hjk
  fin_cases j <;> fin_cases k <;> first
    | exact (hj rfl).elim
    | exact (hk rfl).elim
    | exact False.elim ((show ¬ _ from by decide) hjk)
    | skip
  all_goals symm
  · change SSet.stdSimplex.δ 0 ≫
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct (a ≫ m) b c t ht).simplex =
      SSet.stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictComplexTriangle m b).simplex
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct (a ≫ m) b c t ht).d₀, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictComplexTriangle m b).d₀]
  · change SSet.stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictComplexTriangle a m).simplex =
      SSet.stdSimplex.δ 2 ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictComplexTriangle m b).simplex
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictComplexTriangle a m).d₀, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictComplexTriangle m b).d₂]
  · change SSet.stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictComplexTriangle a m).simplex =
      SSet.stdSimplex.δ 2 ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct (a ≫ m) b c t ht).simplex
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictComplexTriangle a m).d₁, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct (a ≫ m) b c t ht).d₂]

/-- 中間対象の因子分解比較の実際の内部ホーン。 -/
def complexTriangleMiddleHorn : (SSet.horn 3 2 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S) :=
  Classical.choose (complexTriangleMiddleFaces_compatible a m b c t ht).exists_desc

/-- 内部ホーンは指定面を保つ。 -/
lemma complexTriangleMiddleHorn_face (j : Fin 4) (hj : j ≠ 2) :
    SSet.horn.ι 2 j hj ≫ complexTriangleMiddleHorn a m b c t ht =
      complexTriangleMiddleFaces a m b c t ht j hj :=
  Classical.choose_spec (complexTriangleMiddleFaces_compatible a m b c t ht).exists_desc j hj

/-- 最上位成分が零の中間対象比較三単体。 -/
def complexTriangleMiddle : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 3 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.filler S (Complex S) (complexTriangleMiddleHorn a m b c t ht) (by decide) (by decide)

/-- 三単体は三つの指定面を保つ。 -/
lemma complexTriangleMiddle_face (j : Fin 4) (hj : j ≠ 2) :
    (complexTriangleMiddle a m b c t ht).pullback (SimplexCategory.δ j).toOrderHom =
      SSet.yonedaEquiv (complexTriangleMiddleFaces a m b c t ht j hj) := by
  calc
    _ = (complexTriangleMiddleHorn a m b c t ht).app _ (SSet.horn.face 2 j hj) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.filler_face S (Complex S) _ _ _ j hj
    _ = _ := by
      have hh := congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)))
        (complexTriangleMiddleHorn_face a m b c t ht j hj)
      rw [SSet.yonedaEquiv_comp] at hh
      exact hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories
