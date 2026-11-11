module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativeHomControl
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges

/-!
概要：元の二射と、合成端だけを固定した全長 Hom から実二胞体を作る。
方針：厳密合成の二単体の長い Hom だけを置き換える。
規約：指定された二射と全 native Hom を厳密に回収する。局所 Kan 性は不要。
使われ方：Ind-S (9) の各入力点における制御二胞体。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits


variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- 厳密合成の全長 native Hom は元の合成射に定値。 -/
lemma coherentNerveCompStruct_native_const :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).simplex.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ =
      SSet.const (SimplicialCategory.homEquiv' X Z (f ≫ g)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

variable (m : nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} ⟶ SimplicialCategory.sHom X Z)
  (hm : m.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath) =
    SimplicialCategory.homEquiv' X Z (f ≫ g))

include hm in
/-- 指定全長 Hom は、元の二短辺の豊穣合成条件を満たす。 -/
lemma controlledNativeTriangle_comp :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 3)) (ULift.up 1) (ULift.up 2) ≫ m =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).simplex.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩ ⊗ₘ
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).simplex.map ⟨ULift.up 1⟩ ⟨ULift.up 2⟩) ≫
      eComp SSet X Y Z := by
  calc
    _ = SSet.const (SimplicialCategory.homEquiv' X Z (f ≫ g)) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLongHom_comp_of_full_value m _ hm
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 3)) (ULift.up 1) (ULift.up 2) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).simplex.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ := by
      rw [coherentNerveCompStruct_native_const, SSet.comp_const]
    _ = _ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).simplex.map_comp _ _ _

/-- 指定全長 Hom を持つ、元の二射の制御二胞体。 -/
def controlledNativeTriangle : (SimplicialNerve C) _⦋2⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleWithNativeLongHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).simplex m
    (controlledNativeTriangle_comp f g m hm)

/-- 最初の辺は元の第一射そのもの。 -/
lemma controlledNativeTriangle_first :
    (SimplicialNerve C).δ (2 : Fin 3) (controlledNativeTriangle f g m hm) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge := by
  rw [controlledNativeTriangle, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleWithNativeLongHom_first]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).d₂

/-- 最後の辺は元の第二射そのもの。 -/
lemma controlledNativeTriangle_last :
    (SimplicialNerve C).δ (0 : Fin 3) (controlledNativeTriangle f g m hm) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge := by
  rw [controlledNativeTriangle, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleWithNativeLongHom_last]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).d₀

/-- 元の全 native Hom 写像を厳密に回収する。 -/
lemma controlledNativeTriangle_native :
    (controlledNativeTriangle f g m hm).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ = m :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleWithNativeLongHom_native _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
