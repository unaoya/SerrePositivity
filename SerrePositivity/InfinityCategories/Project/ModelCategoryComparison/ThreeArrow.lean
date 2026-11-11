module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# 三本矢と固定語の zigzag の比較

概要：元の弱同値の両脚を持つ三本矢を、同じ三列の hammock graph へ入れる。
方針：元の四対象・三射・二つの縦射を全てそのまま使う。
規約：端点の縦射は恒等射。三本矢の全縦弱同値は二つのうち三つから得る。
使われ方：既存 Map^h の比較を実際の hammock の固定語へ接続する。
-/

@[expose] public section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

/-- 元の三本矢の同じ四頂点・三列。 -/
def obj (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow X Y where
  vertex := ![X, S.left, S.right, Y]
  first := rfl
  last := rfl
  arrow := Fin.cases S.leftMap (Fin.cases S.middle (Fin.cases S.rightMap (fun i => Fin.elim0 i)))
  backward_mem i hi := by
    fin_cases i
    · exact S.left_mem
    · cases hi
    · exact S.right_mem

/-- 元の全縦射を同じ四成分として扱う。 -/
def map {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj S) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow.obj T) where
  app := Fin.cases (𝟙 X)
    (Fin.cases f.left (Fin.cases f.right (Fin.cases (𝟙 Y) (fun i => Fin.elim0 i))))
  app_mem j := by
    fin_cases j
    · exact (weakEquivalences C).id_mem _
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.left_weakEquivalence f
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.right_weakEquivalence f
    · exact (weakEquivalences C).id_mem _
  first := rfl
  last := rfl
  comm i := by
    fin_cases i
    · exact (Category.comp_id _).trans f.left_w.symm
    · exact f.middle_w
    · exact f.right_w.trans (Category.id_comp _).symm

/-- 元の三本矢から同じ三列の zigzag への関手。 -/
def functor : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow X Y where
  obj := obj
  map := map
  map_id S := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (by
    intro j
    fin_cases j <;> rfl)
  map_comp f g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (by
    intro j
    fin_cases j
    · exact (Category.id_comp _).symm
    · rfl
    · rfl
    · exact (Category.id_comp _).symm)

instance functor_faithful : (functor (X := X) (Y := Y)).Faithful where
  map_injective := by
    intro S T f g h
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext f g
      (congrArg (fun k : functor.obj S ⟶ functor.obj T => k.app 1) h)
      (congrArg (fun k : functor.obj S ⟶ functor.obj T => k.app 2) h)

/-- 同じ三列の縦射から元の二つの中間縦射を回収する。 -/
def preimage {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : functor.obj S ⟶ functor.obj T) : S ⟶ T where
  left := f.app 1
  right := f.app 2
  left_w := by
    have h := f.comm (0 : Fin 3)
    change S.leftMap ≫ f.app 0 = f.app 1 ≫ T.leftMap at h
    have hf : f.app 0 = 𝟙 X := f.first
    rw [hf] at h
    exact h.symm.trans (Category.comp_id S.leftMap)
  middle_w := f.comm (1 : Fin 3)
  right_w := by
    have h := f.comm (2 : Fin 3)
    change S.rightMap ≫ f.app 2 = f.app 3 ≫ T.rightMap at h
    have hf : f.app (3 : Fin 4) = 𝟙 Y := f.last
    rw [hf] at h
    exact h.trans (Category.id_comp T.rightMap)

instance functor_full : (functor (X := X) (Y := Y)).Full where
  map_surjective f := ⟨preimage f, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (by
    intro j
    fin_cases j
    · exact f.first.symm
    · rfl
    · rfl
    · exact f.last.symm)⟩

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow
