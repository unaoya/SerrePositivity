module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleDegeneracy
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanComparisonTetrahedron

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarUnitTriangles

/-!
# 中断した任意モデル源への一般化：OrdinaryBarUnitCoherence

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Native composition with the unit retains both selected comparison edges。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0235][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0235
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Native composition with the unit retains both selected comparison edges

An actual tetrahedron retains the previous composition triangle, the
explicit return triangle made from the unit comparison, and the
degenerate cone triangle. Its fourth face is the required unit
coherence with a strictly constant third edge.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarUnitCoherence
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem OrdinaryBarRelativeHomDescent
open OrdinaryBarUnitTriangles
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

local notation "F" => root hcof hfib P j f c
local notation "L" => leftIntermediate hcof hfib P j f cX c
local notation "R" => rightIntermediate hcof hfib P j f cY c
local notation "sX" => small hcof hfib X
local notation "sY" => small hcof hfib Y
local notation "hK" => SimplexParameterHom.native_kan sX sY
  (OrdinaryBarSmallReference.value_kan hcof hfib Y)

abbrev leftData := ComparisonTriangleDegeneracy.roundTrip F L
  (leftOutgoing hcof hfib P j f cX c) (leftReturn hcof hfib P j f cX c) hK

abbrev rightData := ComparisonTriangleDegeneracy.roundTrip F R
  (rightOutgoing hcof hfib P j f cY c) (rightReturn hcof hfib P j f cY c) hK

abbrev left : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ (ihom sX).obj sY :=
  ComparisonTriangleDegeneracy.family F L
    (leftOutgoing hcof hfib P j f cX c) (leftReturn hcof hfib P j f cX c) hK

abbrev right : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ (ihom sX).obj sY :=
  ComparisonTriangleDegeneracy.family F R
    (rightOutgoing hcof hfib P j f cY c) (rightReturn hcof hfib P j f cY c) hK

lemma left_first : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ left hcof hfib P j f cX c =
    (nativeCompositionComparison hcof hfib P j (identityWord (T := T) X) f cX c c).h := by
  calc
    _ = (KanComparisonTriangle.comparison F L (leftOutgoing hcof hfib P j f cX c)).h :=
      ComparisonTriangleDegeneracy.family_first F L
        (leftOutgoing hcof hfib P j f cX c) (leftReturn hcof hfib P j f cX c) hK
    _ = _ := leftOutgoing_comparison hcof hfib P j f cX c

lemma left_second : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ left hcof hfib P j f cX c =
    lift (nativeUnitComparison hcof hfib P X j cX).h
      (fst T HomotopyBinarySquare.interval ≫
        nativeFamily hcof hfib P j
          (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) c) ≫
            MonoidalClosed.comp sX sX sY := by
  calc
    _ = (KanComparisonTriangle.comparison L F (leftReturn hcof hfib P j f cX c)).h :=
      ComparisonTriangleDegeneracy.family_second F L
        (leftOutgoing hcof hfib P j f cX c) (leftReturn hcof hfib P j f cX c) hK
    _ = _ := leftReturn_comparison hcof hfib P j f cX c

lemma left_constant : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ left hcof hfib P j f cX c =
    fst T HomotopyBinarySquare.interval ≫ nativeFamily hcof hfib P j
      (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) c :=
  ComparisonTriangleDegeneracy.family_constant F L
    (leftOutgoing hcof hfib P j f cX c) (leftReturn hcof hfib P j f cX c) hK

lemma right_first : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ right hcof hfib P j f cY c =
    (nativeCompositionComparison hcof hfib P j f (identityWord (T := T) Y) c cY c).h := by
  calc
    _ = (KanComparisonTriangle.comparison F R (rightOutgoing hcof hfib P j f cY c)).h :=
      ComparisonTriangleDegeneracy.family_first F R
        (rightOutgoing hcof hfib P j f cY c) (rightReturn hcof hfib P j f cY c) hK
    _ = _ := rightOutgoing_comparison hcof hfib P j f cY c

lemma right_second : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ right hcof hfib P j f cY c =
    lift (fst T HomotopyBinarySquare.interval ≫ nativeFamily hcof hfib P j
      (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) c)
      (nativeUnitComparison hcof hfib P Y j cY).h ≫ MonoidalClosed.comp sX sY sY := by
  calc
    _ = (KanComparisonTriangle.comparison R F (rightReturn hcof hfib P j f cY c)).h :=
      ComparisonTriangleDegeneracy.family_second F R
        (rightOutgoing hcof hfib P j f cY c) (rightReturn hcof hfib P j f cY c) hK
    _ = _ := rightReturn_comparison hcof hfib P j f cY c

lemma right_constant : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ right hcof hfib P j f cY c =
    fst T HomotopyBinarySquare.interval ≫ nativeFamily hcof hfib P j
      (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) c :=
  ComparisonTriangleDegeneracy.family_constant F R
    (rightOutgoing hcof hfib P j f cY c) (rightReturn hcof hfib P j f cY c) hK

lemma left_retains_triangle : SSet.stdSimplex.δ (2 : Fin 4) ≫
    (leftData hcof hfib P j f cX c).tetrahedron =
      (compositionTriangle hcof hfib P j (identityWord (T := T) X) f cX c c).triangle :=
  (leftData hcof hfib P j f cX c).face_two

lemma right_retains_triangle : SSet.stdSimplex.δ (2 : Fin 4) ≫
    (rightData hcof hfib P j f cY c).tetrahedron =
      (compositionTriangle hcof hfib P j f (identityWord (T := T) Y) c cY c).triangle :=
  (rightData hcof hfib P j f cY c).face_two

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarUnitCoherence
