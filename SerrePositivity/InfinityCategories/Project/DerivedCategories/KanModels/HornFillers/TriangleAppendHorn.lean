module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.ComplexTrianglePostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Quasicategory

/-! # 三角形への後合成を表す三次内部ホーン

概要：元の三角形と後合成射を、三つの既知面を持つ内部ホーンへ組み立てる。
方針：厳密な合成三角形二つと元の三角形を貼り、最上位が零の既存充填を使う。
規約：欠けた面の同定は後続。使われ方：D7 の双対比較三単体。
-/
@[expose] public section
open CategoryTheory SerrePositivity.DifferentialGraded

open CochainComplex HomComplex
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
variable {S : Type u} [CommRing S] {W X Y Z : Complex S}
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 二射の厳密合成を零ホモトピーで表す三角形。 -/
def strictComplexTriangle (b : X ⟶ Y) (q : Y ⟶ Z) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct b q (b ≫ q) 0 (by simp only [δ_zero, sub_self])
/-- 後合成の三次ホーンの各既知面。 -/
def complexTriangleAppendFaces (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (q : Y ⟶ Z) :
    ∀ (j : Fin 4) (_ : j ≠ 2), (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S) := fun j _ =>
  ![SSet.yonedaEquiv.symm (strictComplexTriangle b q).simplex,
    SSet.yonedaEquiv.symm (strictComplexTriangle c q).simplex,
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.postcomposeComplexTriangle a b c t ht q),
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct a b c t ht).simplex] j
/-- 三つの既知面は共通の辺で一致する。 -/
lemma complexTriangleAppendFaces_compatible (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (q : Y ⟶ Z) :
    SSet.horn.IsCompatible (complexTriangleAppendFaces a b c t ht q) := by
  intro j k hj hk hjk
  fin_cases j <;> fin_cases k <;> first
    | exact (hj rfl).elim
    | exact (hk rfl).elim
    | exact False.elim ((show ¬ _ from by decide) hjk)
    | skip
  all_goals symm
  · change SSet.stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm (strictComplexTriangle c q).simplex =
      SSet.stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm (strictComplexTriangle b q).simplex
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      (strictComplexTriangle c q).d₀, (strictComplexTriangle b q).d₀]
  · change SSet.stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct a b c t ht).simplex =
      SSet.stdSimplex.δ 2 ≫ SSet.yonedaEquiv.symm (strictComplexTriangle b q).simplex
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct a b c t ht).d₀, (strictComplexTriangle b q).d₂]
  · change SSet.stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct a b c t ht).simplex =
      SSet.stdSimplex.δ 2 ≫ SSet.yonedaEquiv.symm (strictComplexTriangle c q).simplex
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct a b c t ht).d₁, (strictComplexTriangle c q).d₂]
/-- 後合成を表す実際の三次内部ホーン。 -/
def complexTriangleAppendHorn (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (q : Y ⟶ Z) :
    (SSet.horn 3 2 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S) :=
  Classical.choose (complexTriangleAppendFaces_compatible a b c t ht q).exists_desc
/-- ホーン写像の各面は指定した既知面。 -/
lemma complexTriangleAppendHorn_face (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (q : Y ⟶ Z)
    (j : Fin 4) (hj : j ≠ 2) :
    SSet.horn.ι 2 j hj ≫ complexTriangleAppendHorn a b c t ht q =
      complexTriangleAppendFaces a b c t ht q j hj :=
  Classical.choose_spec (complexTriangleAppendFaces_compatible a b c t ht q).exists_desc j hj

/-- 三つの既知面を持つ、最上位成分が零の比較三単体。 -/
def complexTriangleAppend (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (q : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 3 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.filler S (Complex S) (complexTriangleAppendHorn a b c t ht q) (by decide) (by decide)
/-- 比較三単体は各既知面を保つ。 -/
lemma complexTriangleAppend_face (a : W ⟶ X) (b : X ⟶ Y) (c : W ⟶ Y)
    (t : Cochain W Y (-1))
    (ht : δ (-1) 0 t = Cochain.ofHom (a ≫ b) - Cochain.ofHom c) (q : Y ⟶ Z)
    (j : Fin 4) (hj : j ≠ 2) :
    (complexTriangleAppend a b c t ht q).pullback (SimplexCategory.δ j).toOrderHom =
      SSet.yonedaEquiv (complexTriangleAppendFaces a b c t ht q j hj) := by
  calc
    _ = (complexTriangleAppendHorn a b c t ht q).app _ (SSet.horn.face 2 j hj) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.filler_face S (Complex S) _ _ _ j hj
    _ = _ := by
      have hh := congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)))
        (complexTriangleAppendHorn_face a b c t ht q j hj)
      rw [SSet.yonedaEquiv_comp] at hh
      exact hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories
