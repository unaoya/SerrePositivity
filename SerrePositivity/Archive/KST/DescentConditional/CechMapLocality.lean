module

public import SerrePositivity.Archive.KST.DescentConditional.CechBaseChangeSpaces

/-!
# 指定 Čech 降下による射の局所的な弱同値の反映

## 概要
両側が指定 Čech 降下を満たす自然な射は、各段での弱同値から基底での弱同値を反映する。

## 方針
実際の指定比較の自然性を用い、ホモトピー極限が保つ段ごとの弱同値と二つの降下比較を消去する。

## 規約
指定の実際の比較を使い、次数ごとの極限と π_* を交換しない。

## 使われ方
論文 補題 3.2 の局所自由 chart での rank 公式の反映と、補題 3.3 の貼り合わせ。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

section Comparison

variable (K : Type u) [SmallCategory K] [ModelCategory SSet.{u}]
  (I J : MorphismProperty SSet.{u}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{u})]

/-- 概要：両側の実降下と各点の弱同値から増強元の射も弱同値（補題 3.2・3.3）。
方針：指定比較の自然性と実際のホモトピー極限による弱同値の保存を使う。
規約：図式の fibrancy は不要。使われ方：前層の射の基底上の局所的な検査。 -/
theorem cechSpaceMap_left_weak_of_descent {A B : AugmentedCechDiagram K} (a : A ⟶ B)
    (hA : HasCechSpaceDescent K I J A) (hB : HasCechSpaceDescent K I J B)
    (hr : ∀ k, weakEquivalences SSet.{u} (a.right.app k)) :
    weakEquivalences SSet.{u} a.left := by
  have hm := HomotopyCones.map_weakEquivalence K I J a.right hr
  have he := (homotopyCechAugmentation K I J).naturality a
  have hc : weakEquivalences SSet.{u}
      (a.left ≫ (homotopyCechAugmentation K I J).app B) :=
    Eq.mpr (congrArg (fun t : A.left ⟶ (HomotopyCones.functor K I J).obj B.right ↦
      weakEquivalences SSet.{u} t) he)
      ((weakEquivalences SSet.{u}).comp_mem _ _ hA hm)
  exact (weakEquivalences SSet.{u}).of_postcomp _ _ hB hc

end Comparison

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {X Y : C} (g : X ⟶ Y) {F G : Cᵒᵖ ⥤ SSet.{0}} (a : F ⟶ G)
  [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{0})]

/-- 概要：元の前層の射の Čech 各段の弱同値は基底の弱同値を反映（補題 3.2）。
方針：全自然な指定空間図式の関手で射を写し、両側の実降下を元の Čech の指定同型で移す。
規約：両側が元の被覆で実際に降下することを入力する。使われ方：Zariski 局所的な rank 作用の検査。 -/
theorem cechPresheafMap_weak_on_base
    (hF : HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace g F))
    (hG : HasCechSpaceDescent SimplexCategory I J (cechAugmentedPresheafSpace g G))
    (hlocal : ∀ n : SimplexCategory,
      weakEquivalences SSet.{0} (a.app (op ((Arrow.mk g).cechNerve.obj (op n))))) :
    weakEquivalences SSet.{0} (a.app (op Y)) := by
  let T := presheafCosimplicialSpaces (cechOverDiagram g) (𝟭 SSet.{0})
  let m := T.map (Functor.whiskerLeft (Over.forget Y).op a)
  have hA := (cechSpaceDescent_iso_iff SimplexCategory I J
    (cechOverPresheafSpaceIso (𝟭 SSet.{0}) g F)).mpr hF
  have hB := (cechSpaceDescent_iso_iff SimplexCategory I J
    (cechOverPresheafSpaceIso (𝟭 SSet.{0}) g G)).mpr hG
  exact cechSpaceMap_left_weak_of_descent SimplexCategory I J m hA hB hlocal

end SerrePositivity.KST.Descent
