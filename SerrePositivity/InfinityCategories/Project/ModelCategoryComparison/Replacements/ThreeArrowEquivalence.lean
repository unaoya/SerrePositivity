module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ThreeArrow
public import SerrePositivity.EInfinity.FrameHom.NerveEquivalenceImage

/-!
# 元の三本矢と三列の hammock graph の圏同値

概要：任意の三列の zigzag の端点を正規化し、元の三本矢の圏へ戻す。
方針：両端の等式を eqToHom で移し、四頂点の明示的な同型を作る。
規約：同値の順関手は既存の四対象・三射を保持する元の包含。
使われ方：Map^h の比較の終域を実際の固定語の hammock graph へ移す。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

/-- 三列の zigzag の同じ内部二対象から元の三本矢を回収。 -/
def recoverObj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow X Y) :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y where
  left := S.vertex 1
  right := S.vertex 2
  leftMap := S.arrow (0 : Fin 3) ≫ eqToHom S.first
  middle := S.arrow (1 : Fin 3)
  rightMap := eqToHom S.last.symm ≫ S.arrow (2 : Fin 3)
  left_mem := (weakEquivalences C).comp_mem _ _ (S.backward_mem (0 : Fin 3) rfl)
    ((weakEquivalences C).of_isIso _)
  right_mem := (weakEquivalences C).comp_mem _ _ ((weakEquivalences C).of_isIso _)
    (S.backward_mem (2 : Fin 3) rfl)

/-- 回収した三本矢の元の zigzag への同型の順射。 -/
def normalizationHom (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow X Y) :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor.obj (recoverObj S) ⟶ S where
  app := Fin.cases (eqToHom S.first.symm)
    (Fin.cases (𝟙 _) (Fin.cases (𝟙 _) (Fin.cases (eqToHom S.last.symm)
      (fun i => Fin.elim0 i))))
  app_mem j := by
    fin_cases j
    · exact (weakEquivalences C).of_isIso (eqToHom S.first.symm)
    · exact (weakEquivalences C).id_mem _
    · exact (weakEquivalences C).id_mem _
    · exact (weakEquivalences C).of_isIso (eqToHom S.last.symm)
  first := rfl
  last := rfl
  comm i := by
    fin_cases i
    · change (S.arrow (0 : Fin 3) ≫ eqToHom S.first) ≫ eqToHom S.first.symm =
        𝟙 _ ≫ S.arrow (0 : Fin 3)
      simp
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact Category.comp_id _

/-- 同じ四成分の同型の逆射。 -/
def normalizationInv (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow X Y) :
    S ⟶ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor.obj (recoverObj S) where
  app := Fin.cases (eqToHom S.first)
    (Fin.cases (𝟙 _) (Fin.cases (𝟙 _) (Fin.cases (eqToHom S.last)
      (fun i => Fin.elim0 i))))
  app_mem j := by
    fin_cases j
    · exact (weakEquivalences C).of_isIso (eqToHom S.first)
    · exact (weakEquivalences C).id_mem _
    · exact (weakEquivalences C).id_mem _
    · exact (weakEquivalences C).of_isIso (eqToHom S.last)
  first := rfl
  last := rfl
  comm i := by
    fin_cases i
    · exact (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · change S.arrow (2 : Fin 3) ≫ 𝟙 _ =
        eqToHom S.last ≫ eqToHom S.last.symm ≫ S.arrow (2 : Fin 3)
      simp

/-- 端点の等式を移しただけの、元の全頂点の同型。 -/
def normalizationIso (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow X Y) :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor.obj (recoverObj S) ≅ S where
  hom := normalizationHom S
  inv := normalizationInv S
  hom_inv_id := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (by
    intro j
    fin_cases j
    · change eqToHom S.first.symm ≫ eqToHom S.first = 𝟙 X
      simp
    · exact Category.id_comp _
    · exact Category.id_comp _
    · change eqToHom S.last.symm ≫ eqToHom S.last = 𝟙 Y
      simp)
  inv_hom_id := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (by
    intro j
    fin_cases j
    · change eqToHom S.first ≫ eqToHom S.first.symm = 𝟙 _
      simp
    · exact Category.id_comp _
    · exact Category.id_comp _
    · change eqToHom S.last ≫ eqToHom S.last.symm = 𝟙 _
      simp)

instance functor_essSurj : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor (X := X) (Y := Y)).EssSurj where
  mem_essImage S := ⟨recoverObj S, ⟨normalizationIso S⟩⟩

instance functor_isEquivalence : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor (X := X) (Y := Y)).IsEquivalence where

/-- 順関手が元の包含に一致する、元の三本矢と三列の zigzag の圏同値。 -/
def equivalence (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y ≌ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow X Y :=
  (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor (X := X) (Y := Y)).asEquivalence

/-- 元の包含の nerve そのものは anodyne 局所化で可逆。 -/
lemma nerveMap_localized_isIso (X Y : C) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.functor (X := X) (Y := Y)))) :=
  (_root_.SerrePositivity.EInfinity.FrameHom.NerveEquivalenceImage.imageIso (equivalence X Y)
    SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ
    (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
