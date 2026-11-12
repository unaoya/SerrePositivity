module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictNativeConeLeg
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CosliceTransport

/-!
概要：strict coherent 錐の三角形の三つの境界射の回収。
方針：指定した錐と円柱の面の厳密な等式を使う。
規約：三角形や辺を新しく選択しない。
使われ方：三つの比較三単体の指定同型の合成関係。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {I : Type u} [SmallCategory I] {C : Type v}
  [Category.{u} C] [SimplicialCategory C] {F : I ⥤ C}
/-- 概要：strict な錐の三角形の底辺は元の図式の射。
方針：錐の三角形の面と通常の脚の式を合わせる。
規約：対象と Hom の宇宙を独立に扱う。
使われ方：比較先の錐の指定三角形の同型の構成。 -/
lemma nativeConeTriangle_strict_zero (c : Cone F) {i j : I} (f : i ⟶ j) :
    (SimplicialNerve C).δ 0
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c)
          (ULift.up (nerve.edgeMk f).edge)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (F.map f)).edge :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeTriangle_zero _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictCoherentDiagram_edge _ f)
/-- 概要：strict な錐の三角形の長辺は通常の錐の終域への脚。
方針：錐の三角形の面と通常の脚の式を合わせる。
規約：対象と Hom の宇宙を独立に扱う。
使われ方：比較先の錐の指定三角形の同型の構成。 -/
lemma nativeConeTriangle_strict_one (c : Cone F) {i j : I} (f : i ⟶ j) :
    (SimplicialNerve C).δ 1
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c)
          (ULift.up (nerve.edgeMk f).edge)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (c.π.app j)).edge := by
  let J := (SSet.uliftFunctor.{v, u}).obj (nerve I)
  have hk : J.δ 0 (ULift.up (nerve.edgeMk f).edge) = ULift.up (ComposableArrows.mk₀ j) := by
    apply ULift.ext
    exact (nerve.edgeMk f).tgt_eq
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeTriangle_face (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c)
    (ULift.up (nerve.edgeMk f).edge) (0 : Fin 2)
  exact h.trans ((congrArg (fun k : J _⦋0⦌ ↦
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) k).edge) hk).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.nativeConeLeg_strict c j))
/-- 概要：strict な錐の三角形の最初の辺は通常の錐の始域への脚。
方針：錐の三角形の面と通常の脚の式を合わせる。
規約：対象と Hom の宇宙を独立に扱う。
使われ方：比較先の錐の指定三角形の同型の構成。 -/
lemma nativeConeTriangle_strict_two (c : Cone F) {i j : I} (f : i ⟶ j) :
    (SimplicialNerve C).δ 2
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c)
          (ULift.up (nerve.edgeMk f).edge)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (c.π.app i)).edge := by
  let J := (SSet.uliftFunctor.{v, u}).obj (nerve I)
  have hk : J.δ 1 (ULift.up (nerve.edgeMk f).edge) = ULift.up (ComposableArrows.mk₀ i) := by
    apply ULift.ext
    exact (nerve.edgeMk f).src_eq
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeTriangle_face (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c)
    (ULift.up (nerve.edgeMk f).edge) (1 : Fin 2)
  exact h.trans ((congrArg (fun k : J _⦋0⦌ ↦
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c) k).edge) hk).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.nativeConeLeg_strict c i))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
