module

public import SerrePositivity.InfinityCategories.ModelBridge.ThreeArrowPaddingMaps

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
namespace SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding
open CategoryTheory HomotopicalAlgebra FrameHom

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

def toOuter (S : WeakThreeArrow X Y) : middle S ⟶ outer S where
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

def toInner (S : WeakThreeArrow X Y) : middle S ⟶ inner S where
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
lemma toOuter_naturality_app {S T : WeakThreeArrow X Y} (f : S ⟶ T) (j : Fin 6) :
    (middleMap f).app j ≫ (toOuter T).app j = (toOuter S).app j ≫ (outerMap f).app j := by
    fin_cases j
    · rfl
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.id_comp _).trans f.right_w.symm
    · rfl

lemma toInner_naturality_app {S T : WeakThreeArrow X Y} (f : S ⟶ T) (j : Fin 6) :
    (middleMap f).app j ≫ (toInner T).app j = (toInner S).app j ≫ (innerMap f).app j := by
    fin_cases j
    · rfl
    · exact f.left_w.trans (Category.comp_id _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · rfl
    · rfl

lemma toOuter_naturality {S T : WeakThreeArrow X Y} (f : S ⟶ T) :
    middleMap f ≫ toOuter T = toOuter S ≫ outerMap f :=
  Zigzag.hom_ext _ _ (toOuter_naturality_app f)

lemma toInner_naturality {S T : WeakThreeArrow X Y} (f : S ⟶ T) :
    middleMap f ≫ toInner T = toInner S ≫ innerMap f :=
  Zigzag.hom_ext _ _ (toInner_naturality_app f)

def toOuterNat : middleFunctor (X := X) (Y := Y) ⟶ outerFunctor where
  app := toOuter
  naturality _ _ f := toOuter_naturality f

def toInnerNat : middleFunctor (X := X) (Y := Y) ⟶ innerFunctor where
  app := toInner
  naturality _ _ f := toInner_naturality f

end SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding
