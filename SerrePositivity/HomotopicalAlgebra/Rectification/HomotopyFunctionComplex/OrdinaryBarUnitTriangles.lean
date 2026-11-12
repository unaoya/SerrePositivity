module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.BinaryIntervalTriangles

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleBinary
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ClosedParameterUnits

/-!
# 中断した任意モデル源への一般化：OrdinaryBarUnitTriangles

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Preserve the native composition and unit comparisons in unit triangles。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0236][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0236
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Preserve the native composition and unit comparisons in unit triangles

The outgoing triangles are the previous chosen composition triangles.
The return triangles are explicit parts of the actual binary interval
square. Only endpoint expressions change; whole selected maps remain.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarUnitTriangles
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem OrdinaryBarRelativeHomDescent
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}} {X Y : D C}
  (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
  (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (cX : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X X)
  (cY : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P Y Y)
  (c : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X Y)

abbrev identityWord (A : D C) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶
    OrdinaryBarFixedWordResolution.hom C A A :=
  SSet.stdSimplex.isTerminalObj₀.from _ ≫ OrdinaryBarFixedWordResolution.identity C A

local notation "R" => nativeRestrictionComparison hcof hfib P j
local notation "sX" => small hcof hfib X
local notation "sY" => small hcof hfib Y

abbrev root := R f c
def leftIntermediate : SSet.Homotopy
    (lift (nativeFamily hcof hfib P j
      (identityWord (T := T) X ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X X) cX)
      (nativeFamily hcof hfib P j
        (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) c) ≫
          MonoidalClosed.comp sX sX sY)
    (OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints
    (compositionComparison hcof hfib P j (identityWord (T := T) X) f cX c) rfl
    (congrArg (OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j)
      (OrdinaryBarFixedWordResolution.identity_left C f))

def rightIntermediate : SSet.Homotopy
    (lift (nativeFamily hcof hfib P j
      (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) c)
      (nativeFamily hcof hfib P j
        (identityWord (T := T) Y ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C Y Y) cY) ≫
          MonoidalClosed.comp sX sY sY)
    (OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints
    (compositionComparison hcof hfib P j f (identityWord (T := T) Y) c cY) rfl
    (congrArg (OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j)
      (OrdinaryBarFixedWordResolution.identity_right C f))

def leftOutgoing : KanComparisonTriangle.Data (root hcof hfib P j f c)
    (leftIntermediate hcof hfib P j f cX c) :=
  ComparisonTriangleBinary.changeEdges
    (F' := root hcof hfib P j f c) (G' := leftIntermediate hcof hfib P j f cX c)
    (compositionTriangle hcof hfib P j (identityWord (T := T) X) f cX c c)
    (by change (R (lift (identityWord (T := T) X) f ≫
          OrdinaryBarFixedWordResolution.composition C X X Y) c).h = (R f c).h
        rw [identityWord, OrdinaryBarFixedWordResolution.identity_left])
    (by rw [leftIntermediate, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h])

def rightOutgoing : KanComparisonTriangle.Data (root hcof hfib P j f c)
    (rightIntermediate hcof hfib P j f cY c) :=
  ComparisonTriangleBinary.changeEdges
    (F' := root hcof hfib P j f c) (G' := rightIntermediate hcof hfib P j f cY c)
    (compositionTriangle hcof hfib P j f (identityWord (T := T) Y) c cY c)
    (by change (R (lift f (identityWord (T := T) Y) ≫
          OrdinaryBarFixedWordResolution.composition C X Y Y) c).h = (R f c).h
        rw [identityWord, OrdinaryBarFixedWordResolution.identity_right])
    (by rw [rightIntermediate, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h])

def leftReturn : KanComparisonTriangle.Data (leftIntermediate hcof hfib P j f cX c)
    (root hcof hfib P j f c) :=
  ComparisonTriangleBinary.changeEdges
    (F' := leftIntermediate hcof hfib P j f cX c) (G' := root hcof hfib P j f c)
    (BinaryIntervalTriangles.lower (nativeUnitComparison hcof hfib P X j cX) (R f c)
      (MonoidalClosed.comp sX sX sY))
    (by
      change lift (nativeUnitComparison hcof hfib P X j cX).h (R f c).h ≫
        MonoidalClosed.comp sX sX sY = (leftIntermediate hcof hfib P j f cX c).h
      rw [leftIntermediate, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h,
        compositionComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h]
      change lift (nativeUnitComparison hcof hfib P X j cX).h (R f c).h ≫
        MonoidalClosed.comp sX sX sY =
          lift (R (identityWord (T := T) X) cX).h (R f c).h ≫ MonoidalClosed.comp sX sX sY
      rw [nativeUnitComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h])
    (ClosedParameterUnits.firstFixed_interval (R f c))

def rightReturn : KanComparisonTriangle.Data (rightIntermediate hcof hfib P j f cY c)
    (root hcof hfib P j f c) :=
  ComparisonTriangleBinary.changeEdges
    (F' := rightIntermediate hcof hfib P j f cY c) (G' := root hcof hfib P j f c)
    (BinaryIntervalTriangles.upper (R f c) (nativeUnitComparison hcof hfib P Y j cY)
      (MonoidalClosed.comp sX sY sY))
    (by
      change lift (R f c).h (nativeUnitComparison hcof hfib P Y j cY).h ≫
        MonoidalClosed.comp sX sY sY = (rightIntermediate hcof hfib P j f cY c).h
      rw [rightIntermediate, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h,
        compositionComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h]
      change lift (R f c).h (nativeUnitComparison hcof hfib P Y j cY).h ≫
        MonoidalClosed.comp sX sY sY =
          lift (R f c).h (R (identityWord (T := T) Y) cY).h ≫ MonoidalClosed.comp sX sY sY
      rw [nativeUnitComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h])
    (ClosedParameterUnits.secondFixed_interval (R f c))

lemma leftOutgoing_comparison :
    (KanComparisonTriangle.comparison _ _ (leftOutgoing hcof hfib P j f cX c)).h =
      (nativeCompositionComparison hcof hfib P j (identityWord (T := T) X) f cX c c).h := by
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫
    (leftOutgoing hcof hfib P j f cX c).triangle) =
      uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫
        (compositionTriangle hcof hfib P j (identityWord (T := T) X) f cX c c).triangle)
  rfl

lemma rightOutgoing_comparison :
    (KanComparisonTriangle.comparison _ _ (rightOutgoing hcof hfib P j f cY c)).h =
      (nativeCompositionComparison hcof hfib P j f (identityWord (T := T) Y) c cY c).h := by
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫
    (rightOutgoing hcof hfib P j f cY c).triangle) =
      uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫
        (compositionTriangle hcof hfib P j f (identityWord (T := T) Y) c cY c).triangle)
  rfl

lemma leftReturn_comparison :
    (KanComparisonTriangle.comparison _ _ (leftReturn hcof hfib P j f cX c)).h =
      lift (nativeUnitComparison hcof hfib P X j cX).h
        (fst T HomotopyBinarySquare.interval ≫
          nativeFamily hcof hfib P j
          (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) c) ≫
            MonoidalClosed.comp sX sX sY := by
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫
    (leftReturn hcof hfib P j f cX c).triangle) = _
  have ht : (leftReturn hcof hfib P j f cX c).triangle =
      (BinaryIntervalTriangles.lower (nativeUnitComparison hcof hfib P X j cX) (R f c)
        (MonoidalClosed.comp sX sX sY)).triangle := rfl
  rw [ht]
  exact BinaryIntervalTriangles.lower_comparison (nativeUnitComparison hcof hfib P X j cX) (R f c)
    (MonoidalClosed.comp sX sX sY)

lemma rightReturn_comparison :
    (KanComparisonTriangle.comparison _ _ (rightReturn hcof hfib P j f cY c)).h =
      lift (fst T HomotopyBinarySquare.interval ≫
        nativeFamily hcof hfib P j
          (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) c)
        (nativeUnitComparison hcof hfib P Y j cY).h ≫ MonoidalClosed.comp sX sY sY := by
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫
    (rightReturn hcof hfib P j f cY c).triangle) = _
  have ht : (rightReturn hcof hfib P j f cY c).triangle =
      (BinaryIntervalTriangles.upper (R f c) (nativeUnitComparison hcof hfib P Y j cY)
        (MonoidalClosed.comp sX sY sY)).triangle := rfl
  rw [ht]
  exact BinaryIntervalTriangles.upper_comparison (R f c) (nativeUnitComparison hcof hfib P Y j cY)
    (MonoidalClosed.comp sX sY sY)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarUnitTriangles
