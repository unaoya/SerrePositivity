module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ThreeArrowPaddingMaps

/-!
# 元の中間配置からの二つの縦弱同値の自然変換

概要：中間配置は、元の右脚で外側配置へ、元の左脚で内側配置へ写る。
方針：一頂点だけを動かし、全列の正方形と元の三本矢の縦射への自然性を照合する。
規約：動く縦射は元の脚そのもの。他の全縦射は恒等射。
使われ方：二つの配置の nerve の比較ホモトピー。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

def toOuter (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.middle S ⟶ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.outer S where
  app := Fin.cases (𝟙 X) (Fin.cases (𝟙 S.left) (Fin.cases (𝟙 S.left)
    (Fin.cases (𝟙 S.right) (Fin.cases S.rightMap (Fin.cases (𝟙 Y) (fun i => Fin.elim0 i))))))
  app_mem j := by
    change Fin 6 at j
    fin_cases j
    · exact (weakEquivalences C).id_mem _
    · exact (weakEquivalences C).id_mem _
    · exact (weakEquivalences C).id_mem _
    · exact (weakEquivalences C).id_mem _
    · exact S.right_mem
    · exact (weakEquivalences C).id_mem _
  first := rfl
  last := rfl
  comm i := by
    change Fin 5 at i
    fin_cases i
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · rfl
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · rfl
    · rfl

def toInner (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.middle S ⟶ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.inner S where
  app := Fin.cases (𝟙 X) (Fin.cases S.leftMap (Fin.cases (𝟙 S.left)
    (Fin.cases (𝟙 S.right) (Fin.cases (𝟙 Y) (Fin.cases (𝟙 Y) (fun i => Fin.elim0 i))))))
  app_mem j := by
    change Fin 6 at j
    fin_cases j
    · exact (weakEquivalences C).id_mem _
    · exact S.left_mem
    · exact (weakEquivalences C).id_mem _
    · exact (weakEquivalences C).id_mem _
    · exact (weakEquivalences C).id_mem _
    · exact (weakEquivalences C).id_mem _
  first := rfl
  last := rfl
  comm i := by
    change Fin 5 at i
    fin_cases i
    · rfl
    · rfl
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · rfl

set_option maxHeartbeats 800000 in
-- 依存する6頂点の成分等式の kernel 検査に計算量の上限を局所的に確保する。
lemma toOuter_naturality_app {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) (j : Fin 6) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleMap f).app j ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.toOuter T).app j = (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.toOuter S).app j ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outerMap f).app j := by
    fin_cases j
    · rfl
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.id_comp _).trans f.right_w.symm
    · rfl

lemma toInner_naturality_app {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) (j : Fin 6) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleMap f).app j ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.toInner T).app j = (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.toInner S).app j ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.innerMap f).app j := by
    fin_cases j
    · rfl
    · exact f.left_w.trans (Category.comp_id _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · rfl
    · rfl

lemma toOuter_naturality {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleMap f ≫ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.toOuter T = _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.toOuter S ≫ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outerMap f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (toOuter_naturality_app f)

lemma toInner_naturality {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleMap f ≫ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.toInner T = _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.toInner S ≫ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.innerMap f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (toInner_naturality_app f)

def toOuterNat : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleFunctor (X := X) (Y := Y) ⟶ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.outerFunctor where
  app := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.toOuter
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.toOuter_naturality f

def toInnerNat : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleFunctor (X := X) (Y := Y) ⟶ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.innerFunctor where
  app := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.toInner
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.toInner_naturality f

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
