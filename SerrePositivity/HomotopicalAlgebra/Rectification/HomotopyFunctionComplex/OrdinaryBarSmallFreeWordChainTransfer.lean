module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer

/-!
# 中断した任意モデル源への一般化：OrdinaryBarSmallFreeWordChainTransfer

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Native small parameter families for arbitrary actual free-resolution chains。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0221][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0221
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Native small parameter families for arbitrary actual free-resolution chains

Pulling the entire simplex parameter back to a lifted small parameter and
lowering the resulting tensor family preserves every face and degeneracy,
and both unit/zero composition laws with arbitrary prefixes and suffixes.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ) {T U : SSet.{v}}
  (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ parameters P n)

def family {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ WordSegment.obj)) :
    small hcof hfib X ⊗ T ⟶ small hcof hfib Y :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor (OrdinaryBarFreeWordChainTransfer.family hcof hfib P n j q t)

lemma family_substitute (k : U ⟶ T) {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ WordSegment.obj)) :
    family hcof hfib P n (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map k ≫ j) q (fun r => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map k ≫ t r) =
      ParameterComposition.substitute k (family hcof hfib P n j q t) := by
  rw [family, OrdinaryBarFreeWordChainTransfer.family_substitute]
  ext m x
  rfl

lemma family_nil (X : degree (D C) (n + 1))
    (t : ℕ → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ WordSegment.obj)) :
    family hcof hfib P n j (Quiver.Path.nil : Quiver.Path X X) t = fst (small hcof hfib X) T := by
  rw [family, OrdinaryBarFreeWordChainTransfer.family_nil]
  ext m x
  rfl

lemma family_face (i : Fin (n + 2)) {X Y : degree (D C) (n + 2)} (q : Quiver.Path X Y)
    (t : ℕ → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ WordSegment.obj)) :
    family hcof hfib P n j
      ((FreeGeneratorFaces.fixedFace (D C) (n + 1) i).toPrefunctor.mapPath q) t =
      family hcof hfib P (n + 1) (j ≫ P ◁ SSet.stdSimplex.δ i) q t :=
  congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor
    (OrdinaryBarFreeWordChainTransfer.family_face hcof hfib P n j i q t)

lemma family_degeneracy (i : Fin (n + 1))
    (k : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ parameters P (n + 1))
    {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ WordSegment.obj)) :
    family hcof hfib P (n + 1) k ((degeneracyFunctor (D C) n i).toPrefunctor.mapPath q) t =
      family hcof hfib P n (k ≫ P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i) q t :=
  congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor
    (OrdinaryBarFreeWordChainTransfer.family_degeneracy hcof hfib P n i k q t)

lemma unit_face {a d : D C} {X Y Z : degree (D C) (n + 1)}
    (q : OrdinaryBarWordChainFamily.chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) a X)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (t : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ WordSegment.obj)
    (r : OrdinaryBarWordChainFamily.chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) Z d) :
    OrdinaryBarWordChainFamily.smallFamily hcof hfib
      ((OrdinaryBarFreeWordChainTransfer.snoc hcof hfib P n j
        (OrdinaryBarFreeWordChainTransfer.snoc hcof hfib P n j q f
          (WordSegment.unitAt _)) g t).append r) =
    OrdinaryBarWordChainFamily.smallFamily hcof hfib
      ((OrdinaryBarFreeWordChainTransfer.snoc hcof hfib P n j q (f ≫ g) t).append r) :=
  congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor
    (OrdinaryBarFreeWordChainTransfer.unit_face hcof hfib P n j q f g t r)

lemma zero_face {a d : D C} {X Y : degree (D C) (n + 1)}
    (q : OrdinaryBarWordChainFamily.chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) a X) (f : X ⟶ Y)
    (r : OrdinaryBarWordChainFamily.chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) Y d) :
    OrdinaryBarWordChainFamily.smallFamily hcof hfib
      ((OrdinaryBarFreeWordChainTransfer.snoc hcof hfib P n j q f
        (WordSegment.zeroAt _)).append r) =
    ParameterComposition.comp
      (OrdinaryBarWordChainFamily.smallFamily hcof hfib
        (OrdinaryBarFreeWordChainTransfer.snoc hcof hfib P n j q f (WordSegment.unitAt _)))
      (OrdinaryBarWordChainFamily.smallFamily hcof hfib r) := by
  rw [OrdinaryBarWordChainFamily.smallFamily, OrdinaryBarFreeWordChainTransfer.zero_face]
  ext m x
  rfl

lemma family_ofInterval {X Y : degree (D C) (n + 1)} (q : Quiver.Path X Y)
    (t : ℕ → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) :
    family hcof hfib P n j q (fun k => t k ≫ WordSegment.letter) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor (OrdinaryBarFreeChainTransfer.family hcof hfib P n j q t) :=
  congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor
    (OrdinaryBarFreeWordChainTransfer.family_ofInterval hcof hfib P n j q t)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer
