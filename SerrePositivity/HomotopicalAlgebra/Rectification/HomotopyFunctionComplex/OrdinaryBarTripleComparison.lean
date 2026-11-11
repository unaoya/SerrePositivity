module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleBinary

/-!
# 中断した任意モデル源への一般化：OrdinaryBarTripleComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Four actual comparison intervals for a threefold native composite。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0234][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0234
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Four actual comparison intervals for a threefold native composite

Both bracketings use the original Hom descent choices. Endpoint transport
only uses proved word associativity and the actual native composition
formula; it preserves each whole interval map.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTripleComparison
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem OrdinaryBarRelativeHomDescent
variable {C : Type u} [Category.{v} C] {W X Y Z : D C}

abbrev wordComp {U : SSet.{max u v}} {A B E : D C}
    (f : U ⟶ OrdinaryBarFixedWordResolution.hom C A B)
    (g : U ⟶ OrdinaryBarFixedWordResolution.hom C B E) :=
  lift f g ≫ OrdinaryBarFixedWordResolution.composition C A B E

lemma word_assoc {U : SSet.{max u v}}
    (f : U ⟶ OrdinaryBarFixedWordResolution.hom C W X)
    (g : U ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (h : U ⟶ OrdinaryBarFixedWordResolution.hom C Y Z) :
    wordComp (wordComp f g) h = wordComp f (wordComp g h) := by
  ext n x
  exact Category.assoc (f.app n x) (g.app n x) (h.app n x)

variable [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}}
  (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
  (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C W X)
  (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c₀₁ : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P W X)
  (c₁₂ : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X Y)
  (c₂₃ : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P Y Z)
  (c₀₂ : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P W Y)
  (c₁₃ : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X Z)
  (c₀₃ : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P W Z)

local notation "R" => nativeRestrictionComparison hcof hfib P j
local notation "N" => OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j
local notation "D" => nativeFamily hcof hfib P j
local notation "sW" => small hcof hfib W
local notation "sX" => small hcof hfib X
local notation "sY" => small hcof hfib Y
local notation "sZ" => small hcof hfib Z

abbrev root := R (wordComp (wordComp f g) h) c₀₃

abbrev leftIntermediate := compositionComparison hcof hfib P j (wordComp f g) h c₀₂ c₂₃

def total : SSet.Homotopy
    (lift (lift (D (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C W X) c₀₁)
      (D (g ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) c₁₂) ≫
        MonoidalClosed.comp sW sX sY)
      (D (h ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C Y Z) c₂₃) ≫
        MonoidalClosed.comp sW sY sZ)
    (N (wordComp (wordComp f g) h)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints
    (ClosedHomotopyComposition.comp (ClosedHomotopyComposition.comp (R f c₀₁) (R g c₁₂))
      (R h c₂₃)) rfl (by
        rw [← OrdinaryBarDiagonalClosedAction.nativeFamily_comp hcof hfib P j f g,
          ← OrdinaryBarDiagonalClosedAction.nativeFamily_comp hcof hfib P j (wordComp f g) h])

def rightIntermediate : SSet.Homotopy
    (lift (D (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C W X) c₀₁)
      (D (wordComp g h ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Z) c₁₃) ≫
        MonoidalClosed.comp sW sX sZ)
    (N (wordComp (wordComp f g) h)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints
    (compositionComparison hcof hfib P j f (wordComp g h) c₀₁ c₁₃) rfl
    (congrArg N (word_assoc f g h).symm)

abbrev leftOuterTriangle :=
  compositionTriangle hcof hfib P j (wordComp f g) h c₀₂ c₂₃ c₀₃

def leftInnerTriangle : KanComparisonTriangle.Data
    (leftIntermediate hcof hfib P j f g h c₂₃ c₀₂) (total hcof hfib P j f g h c₀₁ c₁₂ c₂₃) :=
  ComparisonTriangleBinary.changeEdges
    (F' := leftIntermediate hcof hfib P j f g h c₂₃ c₀₂)
    (G' := total hcof hfib P j f g h c₀₁ c₁₂ c₂₃)
    (ComparisonTriangleBinary.right (R (wordComp f g) c₀₂)
      (compositionComparison hcof hfib P j f g c₀₁ c₁₂) (R h c₂₃)
      (MonoidalClosed.comp sW sY sZ) (compositionTriangle hcof hfib P j f g c₀₁ c₁₂ c₀₂))
    (by simp only [leftIntermediate, compositionComparison,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h])
    (by
      change lift (compositionComparison hcof hfib P j f g c₀₁ c₁₂).h (R h c₂₃).h ≫
        MonoidalClosed.comp sW sY sZ = (total hcof hfib P j f g h c₀₁ c₁₂ c₂₃).h
      rw [total, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h]
      change lift (compositionComparison hcof hfib P j f g c₀₁ c₁₂).h (R h c₂₃).h ≫
        MonoidalClosed.comp sW sY sZ =
          lift (ClosedHomotopyComposition.comp (R f c₀₁) (R g c₁₂)).h (R h c₂₃).h ≫
            MonoidalClosed.comp sW sY sZ
      rw [compositionComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h])

def rightOuterTriangle : KanComparisonTriangle.Data
    (root hcof hfib P j f g h c₀₃) (rightIntermediate hcof hfib P j f g h c₀₁ c₁₃) :=
  ComparisonTriangleBinary.changeEdges
    (F' := root hcof hfib P j f g h c₀₃)
    (G' := rightIntermediate hcof hfib P j f g h c₀₁ c₁₃)
    (compositionTriangle hcof hfib P j f (wordComp g h) c₀₁ c₁₃ c₀₃)
    (by change (R (wordComp f (wordComp g h)) c₀₃).h =
          (R (wordComp (wordComp f g) h) c₀₃).h
        rw [word_assoc])
    (by simp only [rightIntermediate, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h])

def rightInnerTriangle : KanComparisonTriangle.Data
    (rightIntermediate hcof hfib P j f g h c₀₁ c₁₃) (total hcof hfib P j f g h c₀₁ c₁₂ c₂₃) :=
  ComparisonTriangleBinary.changeEdges
    (F' := rightIntermediate hcof hfib P j f g h c₀₁ c₁₃)
    (G' := total hcof hfib P j f g h c₀₁ c₁₂ c₂₃)
    (ComparisonTriangleBinary.left (MonoidalClosed.comp sW sX sZ) (R f c₀₁)
      (R (wordComp g h) c₁₃) (compositionComparison hcof hfib P j g h c₁₂ c₂₃)
      (compositionTriangle hcof hfib P j g h c₁₂ c₂₃ c₁₃))
    (by simp only [rightIntermediate, compositionComparison,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h])
    (by
      change lift (R f c₀₁).h (compositionComparison hcof hfib P j g h c₁₂ c₂₃).h ≫
        MonoidalClosed.comp sW sX sZ = (total hcof hfib P j f g h c₀₁ c₁₂ c₂₃).h
      rw [total, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h]
      calc
        _ = (ClosedHomotopyComposition.comp (R f c₀₁)
            (ClosedHomotopyComposition.comp (R g c₁₂) (R h c₂₃))).h := by
          change lift (R f c₀₁).h (compositionComparison hcof hfib P j g h c₁₂ c₂₃).h ≫
            MonoidalClosed.comp sW sX sZ =
              lift (R f c₀₁).h (ClosedHomotopyComposition.comp (R g c₁₂) (R h c₂₃)).h ≫
                MonoidalClosed.comp sW sX sZ
          rw [compositionComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h]
        _ = _ := (ClosedHomotopyComposition.assoc_interval (R f c₀₁) (R g c₁₂) (R h c₂₃)).symm)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTripleComparison
