module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardComposition
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic

/-!
# 閉零射の圏上の標準 Hom の豊穣構造

概要：閉零射の圏の対象に標準 DK Hom と AW 合成を備えた豊穣圏構造を作る。
方針：cartesian tensor の各単体を評価して AW の単位則と結合律を適用する。
規約：通常の圏との射の比較は別途 EnrichedOrdinaryCategory で与える。
使われ方：HA 1.3.1.13–1.3.1.14 の C_Δ の構成。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded MonoidalCategory
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：閉零射の圏の対象を標準 DK Hom で単体的に豊穣化する。
方針：単位写像と AW 合成を指定し、各次数で単位則と結合律を確認する。
規約：Hom の宇宙は係数環の宇宙 u である。
使われ方：HA 1.3.1.13 の単体的圏 C_Δ。 -/
@[instance_reducible]
def standardEnrichedCategory : EnrichedCategory SSet.{u} (ClosedCategory R D) where
  Hom x y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y
  id x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnitMap (R := R) (D := D) x
  comp x y z := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardComposition (R := R) (D := D) x y z
  id_comp x y := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro f
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW_unit_right f
  comp_id x y := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro f
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW_unit_left f
  assoc w x y z := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW_assoc s.2.2 s.2.1 s.1

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
