module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.EdgeHomotopy

/-! # 閉零射の合成と辺の合成

概要：閉零射の圏の合成を通常順の斉次合成と同定し、零ホモトピーの三角形を構成する。
方針：単位からの tensor の次数零評価と、既に構成した三角形の対応を使う。
規約：HA Example 1.3.1.8、Kerodon §2.5.3（Tag 00PK）。使われ方：H⁰ との比較関手の合成保存。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory MonoidalCategory DifferentialGraded
open CategoryTheory.SimplicialObject.Truncated
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：閉零圏の恒等射の次数零評価は dg 単位。
方針：豊穣忘却圏の恒等射の定義を評価する。
規約：HA Example 1.3.1.8。使われ方：比較関手の恒等射の保存。 -/
lemma closedHom_id (x : ClosedCategory A D) :
    closedHomEquiv A D x x (𝟙 x) = unitElement A (ForgetEnrichment.to (Complex A) x) := by
  apply Subtype.ext
  change (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (𝟙 x))).val = _
  rw [ForgetEnrichment.homTo_id]
  rfl

/-- 概要：閉零圏の合成の次数零評価は通常順の斉次合成。
方針：豊穣忘却圏の tensor 合成を単位の一に評価し、次数零の Koszul 符号を除く。
規約：HA Example 1.3.1.8。使われ方：閉零圏の合成から dg nerve の三角形を作る。 -/
lemma closedHom_comp {x y z : ClosedCategory A D} (f : x ⟶ y) (g : y ⟶ z) :
    (closedHomEquiv A D x z (f ≫ g)).val =
      compose A (closedHomEquiv A D y z g).val (closedHomEquiv A D x y f).val (by decide) := by
  change (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (f ≫ g))).val = _
  rw [ForgetEnrichment.homTo_comp, cycleFromUnit_postcomp]
  change (eComp (Complex A) _ _ _).f 0
    (((λ_ (𝟙_ (Complex A))).inv ≫
      (ForgetEnrichment.homTo (Complex A) f ⊗ₘ
        ForgetEnrichment.homTo (Complex A) g)).f 0 (1 : A)) = _
  rw [unit_tensor_apply]
  simp only [compose, forward, closedHomEquiv, unitCycleEquiv, Int.mul_zero,
    Int.negOnePow_zero, one_smul]
  rfl

/-- 概要：恒等辺から作った閉零射は閉零圏の恒等射。
方針：閉零元との同値の単射性と単位の計算を使う。
規約：HA Example 1.3.1.8。使われ方：ホモトピー圏比較の恒等射の保存。 -/
lemma edgeClosed_id (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (SSet.Truncated.Edge.id x) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.vertexClosed x) := by
  apply (closedHomEquiv A D _ _).injective
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeCycle_id, closedHom_id]
  rfl

/-- 概要：二つの辺の閉零射を実際に合成して対応する対角辺を作る。
方針：閉零圏の合成を、端点固定の辺との同値の逆で戻す。
規約：HA Example 1.3.1.8。使われ方：選択された辺の合成と実際の dg 合成の比較。 -/
def strictComp {x y z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂}
    (f : SSet.Truncated.Edge x y) (g : SSet.Truncated.Edge y z) : SSet.Truncated.Edge x z :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeClosedEquiv x z).symm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed f ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed g)

/-- 概要：実際の閉零合成から作った対角辺を閉零射へ戻すと元の合成になる。
方針：辺と閉零射の同値の右逆則を使う。
規約：HA Example 1.3.1.8。使われ方：合成構造と比較関手の合成保存。 -/
lemma edgeClosed_strictComp {x y z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂}
    (f : SSet.Truncated.Edge x y) (g : SSet.Truncated.Edge y z) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (strictComp f g) = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed f ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed g :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeClosedEquiv x z).apply_symm_apply _

/-- 概要：実際の合成辺を対角辺とする三角形を、零ホモトピーで構成する。
方針：閉零射の合成の評価を使い、合成と対角辺の差を零にする。
規約：HA Example 1.3.1.8。使われ方：任意に選ばれた辺の合成との一意性による比較。 -/
def strictCompStruct {x y z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂}
    (f : SSet.Truncated.Edge x y) (g : SSet.Truncated.Edge y z) :
    SSet.Truncated.Edge.CompStruct f g (strictComp f g) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compStructOfHomotopy f g (strictComp f g) 0
  rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle (strictComp f g), edgeClosed_strictComp, closedHom_comp,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle]
  simp only [sub_self]
  exact map_zero _

/-- 概要：Mathlib が選ぶ辺の合成は、実際の閉零合成から作った辺と左ホモトピック。
方針：二つの合成構造の同じ二辺に対する一意性を適用する。
規約：Kerodon §2.5.3（Tag 00PK）、HA Example 1.3.1.8。使われ方：商上の合成の保存。 -/
lemma comp_homotopic_strictComp {x y z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂}
    (f : SSet.Truncated.Edge x y) (g : SSet.Truncated.Edge y z) :
    SSet.Truncated.HomotopicL (f.comp g) (strictComp f g) :=
  (SSet.Truncated.Edge.compStruct f g).comp_unique (strictCompStruct f g) .refl .refl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
