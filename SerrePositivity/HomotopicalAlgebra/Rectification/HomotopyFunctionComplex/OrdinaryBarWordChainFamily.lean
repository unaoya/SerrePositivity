module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRetractTransfer
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordRetractChainFamily
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChainFamily

/-!
# 中断した任意モデル源への一般化：OrdinaryBarWordChainFamily

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual word-parameter chain families and their small transfers。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0239][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0239
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual word-parameter chain families and their small transfers

Internal identities are eliminated by concatenating arbitrary neighboring
word parameters. All results use only the small simplicial-set model.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordChainFamily
open OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev chain (T : SSet.{max u v}) (b c : Cᵒᵖ × C) :=
  WordRetractChainFamily.Chain (ambient hcof hfib) T b c

abbrev family {T : SSet.{max u v}} {b c : Cᵒᵖ × C} (q : chain hcof hfib T b c) :=
  WordRetractChainFamily.transfer (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (section_fac hcof hfib) (contraction hcof hfib)
    (contraction_over hcof hfib) (contraction_on_section hcof hfib) q

lemma family_substitute {T U : SSet.{max u v}} {b c : Cᵒᵖ × C}
    (j : U ⟶ T) (q : chain hcof hfib T b c) :
    family hcof hfib (q.substitute j) =
      ParameterComposition.substitute j (family hcof hfib q) :=
  WordRetractChainFamily.transfer_substitute _ _ _ _ _ _ _ _ j q

lemma family_unit_face {T : SSet.{max u v}} {a b c d e : Cᵒᵖ × C}
    (q : chain hcof hfib T a b) (f : ambient hcof hfib b ⟶ ambient hcof hfib c)
    (g : ambient hcof hfib c ⟶ ambient hcof hfib d) (t : T ⟶ WordSegment.obj)
    (r : chain hcof hfib T d e) :
    family hcof hfib (((q.snoc f (WordSegment.unitAt T)).snoc g t).append r) =
      family hcof hfib ((q.snoc (f ≫ g) t).append r) :=
  WordRetractChainFamily.unit_face _ _ _ _ _ _ _ _ q f g t r

lemma family_zero_face {T : SSet.{max u v}} {a b c d : Cᵒᵖ × C}
    (q : chain hcof hfib T a b) (f : ambient hcof hfib b ⟶ ambient hcof hfib c)
    (r : chain hcof hfib T c d) :
    family hcof hfib ((q.snoc f (WordSegment.zeroAt T)).append r) =
      ParameterComposition.comp
        (family hcof hfib (q.snoc f (WordSegment.unitAt T))) (family hcof hfib r) :=
  WordRetractChainFamily.zero_face _ _ _ _ _ _ _ _ q f r

def smallFamily {T : SSet.{v}} {b c : Cᵒᵖ × C}
    (q : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) b c) :
    small hcof hfib b ⊗ T ⟶ small hcof hfib c :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor (family hcof hfib q)

lemma smallFamily_substitute {T U : SSet.{v}} {b c : Cᵒᵖ × C}
    (j : U ⟶ T) (q : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) b c) :
    smallFamily hcof hfib (q.substitute (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map j)) =
      ParameterComposition.substitute j (smallFamily hcof hfib q) := by
  rw [smallFamily, family_substitute]
  ext n x
  rfl

lemma smallFamily_zero_face {T : SSet.{v}} {a b c d e : Cᵒᵖ × C}
    (q : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) a b)
    (f : ambient hcof hfib b ⟶ ambient hcof hfib c)
    (g : ambient hcof hfib c ⟶ ambient hcof hfib d)
    (t : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ WordSegment.obj)
    (r : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) d e) :
    smallFamily hcof hfib (((q.snoc f (WordSegment.unitAt _)).snoc g t).append r) =
      smallFamily hcof hfib ((q.snoc (f ≫ g) t).append r) :=
  congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor (family_unit_face hcof hfib q f g t r)

lemma smallFamily_one_face {T : SSet.{v}} {a b c d : Cᵒᵖ × C}
    (q : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) a b)
    (f : ambient hcof hfib b ⟶ ambient hcof hfib c)
    (r : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) c d) :
    smallFamily hcof hfib ((q.snoc f (WordSegment.zeroAt _)).append r) =
      ParameterComposition.comp
        (smallFamily hcof hfib (q.snoc f (WordSegment.unitAt _)))
        (smallFamily hcof hfib r) := by
  rw [smallFamily, family_zero_face]
  ext n x
  rfl

lemma interior_identity {T : SSet.{max u v}} {a b c d : Cᵒᵖ × C}
    (q : chain hcof hfib T a b) (f : ambient hcof hfib b ⊗ T ⟶ ambient hcof hfib c)
    (t w : T ⟶ WordSegment.obj) (r : chain hcof hfib T c d) :
    family hcof hfib
      (((q.familySnoc f t).familySnoc
        (ParameterComposition.const T (𝟙 (ambient hcof hfib c))) w).append r) =
      family hcof hfib ((q.familySnoc f (lift t w ≫ WordSegment.mul)).append r) :=
  WordRetractChainFamily.interior_identity _ _ _ _ _ _ _ _ q f t w r

lemma small_interior_identity {T : SSet.{v}} {a b c d : Cᵒᵖ × C}
    (q : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) a b)
    (f : ambient hcof hfib b ⊗ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ ambient hcof hfib c)
    (t w : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ WordSegment.obj)
    (r : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) c d) :
    smallFamily hcof hfib
      (((q.familySnoc f t).familySnoc
        (ParameterComposition.const _ (𝟙 (ambient hcof hfib c))) w).append r) =
      smallFamily hcof hfib ((q.familySnoc f (lift t w ≫ WordSegment.mul)).append r) :=
  congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor (interior_identity hcof hfib q f t w r)

lemma family_ofInterval {T : SSet.{max u v}} {a b : Cᵒᵖ × C}
    (q : OrdinaryBarChainFamily.chain hcof hfib T a b) :
    family hcof hfib (WordRetractChainFamily.Chain.ofInterval q) =
      OrdinaryBarChainFamily.family hcof hfib q :=
  WordRetractChainFamily.transfer_ofInterval _ _ _ _ _ _ _ _ q

lemma smallFamily_ofInterval {T : SSet.{v}} {a b : Cᵒᵖ × C}
    (q : OrdinaryBarChainFamily.chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) a b) :
    smallFamily hcof hfib (WordRetractChainFamily.Chain.ofInterval q) =
      OrdinaryBarChainFamily.smallFamily hcof hfib q :=
  congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor (family_ofInterval hcof hfib q)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordChainFamily
