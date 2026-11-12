module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLifting

/-!
# 宇宙liftの前後の実際の区間ホモトピー類の全単射を構成する

## 概要
宇宙liftの前後の実際の区間ホモトピー類の全単射を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。
[棚卸し m0596][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0596
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Reflection of actual homotopies and comparison of their classes across universes
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.UniverseLift

def lowerHomotopy {X K : SSet.{v}} {f g : X ⟶ K}
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} g)) : SSet.Homotopy f g where
  h := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerSimplexTensor H.h
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.down (congrArg (fun k => k.app n ⟨x⟩) H.h₀)
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.down (congrArg (fun k => k.app n ⟨x⟩) H.h₁)
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

/-- 宇宙liftの前後の実際の区間ホモトピー類の全単射を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。
-/
def homotopyClassEquiv (X K : SSet.{v}) :
    HomotopyClasses.obj X K ≃ HomotopyClasses.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} X) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K) where
  toFun := Quot.map _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map (fun _ _ ⟨H⟩ => ⟨_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.homotopy H⟩)
  invFun := Quot.map _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower (fun f g ⟨H⟩ => ⟨lowerHomotopy (f := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower f) (g := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower g) H⟩)
  left_inv x := Quot.inductionOn x (fun _ => rfl)
  right_inv x := Quot.inductionOn x (fun _ => rfl)

@[simp] lemma homotopyClassEquiv_mk {X K : SSet.{v}} (f : X ⟶ K) :
    homotopyClassEquiv.{w} X K (HomotopyClasses.mk f) = HomotopyClasses.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map f) := rfl

lemma homotopyClassEquiv_pre {A X K : SSet.{v}} (i : A ⟶ X) (x : HomotopyClasses.obj X K) :
    homotopyClassEquiv.{w} A K (HomotopyClasses.pre i x) =
      HomotopyClasses.pre (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i) (homotopyClassEquiv X K x) := by
  exact Quot.inductionOn x (fun _ => rfl)

lemma anodyne_map_iff {X Y : SSet.{v}} (i : X ⟶ Y) :
    SSet.anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} i) ↔ SSet.anodyneExtensions i := by
  constructor
  · intro hi A B p hp
    have : HasLiftingProperty (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} p) := hi _ ((horn_rightClass_iff p).mpr hp)
    exact (ModelGeneration.hasLiftingProperty_map_iff SSet.uliftFunctor i p).mp this
  · exact anodyne_map i

end SerrePositivity.SimplicialModel.UniverseLift
