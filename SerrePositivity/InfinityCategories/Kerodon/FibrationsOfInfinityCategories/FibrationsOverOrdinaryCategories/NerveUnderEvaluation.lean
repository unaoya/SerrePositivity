module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveConstantProduct
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveConstantNaturality
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：under-category の nerve と始点の係数値から weighted nerve を評価する。
方針：始点から各対象への射を係数関手で写す自然変換を、定値係数の直積に作用させる。
規約：通常の圏と単体集合値の図式を用い、Kan 性は不要。
使われ方：Kerodon §5.3.3（Tag 025W）、係数の射を weighted nerve の transport とする prism の構成。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：始点の係数値から under-category 上の係数図式への自然変換。
方針：under の対象 c→d に F(c→d) を対応させる。
規約：底の始点 c を固定する。
使われ方：Kerodon §5.3.3（Tag 025W）、同じ係数単体を始点から各対象へ輸送する。 -/
def weightedNerveUnderCoefficient {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    (CategoryTheory.Functor.const (Under c)).obj (F.obj c) ⟶ Under.forget c ⋙ F where
  app d := F.map d.hom
  naturality d e f := by
    change 𝟙 _ ≫ F.map e.hom = F.map d.hom ≫ F.map f.right
    rw [Category.id_comp, ← CategoryTheory.Functor.map_comp, Under.w]

/-- 概要：under の射列と始点の係数単体から元の weighted nerve へ写す。
方針：定値係数の直積を作り、係数の自然変換と底の忘却関手を適用する。
規約：定義域の第一因子は under-category の通常の nerve。
使われ方：Kerodon §5.3.3（Tag 025W）、weighted nerve の transport prism の共通の評価。 -/
def weightedNerveUnderEvaluation {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : nerve (Under c) ⊗ F.obj c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantProduct (Under c) (F.obj c) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (weightedNerveUnderCoefficient F c) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseMap (Under.forget c) F

/-- 概要：under の係数評価は under の忘却による底の射列を被覆する。
方針：定値係数の直積・係数の変換・底変換の射影公式を合成する。
規約：係数の単体は底の射影で忘れる。
使われ方：Kerodon §5.3.3（Tag 025W）、transport prism の底上の式。 -/
lemma weightedNerveUnderEvaluation_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    weightedNerveUnderEvaluation F c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      fst (nerve (Under c)) (F.obj c) ≫ nerveMap (Under.forget c) := by
  rw [weightedNerveUnderEvaluation, Category.assoc, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseMap_projection, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap _),
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap_projection, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantProduct_projection]

/-- 概要：under の一点での係数評価は、指定された射による係数輸送と定値包含の合成。
方針：定値係数の直積の一点での式と、定値包含の二つの自然性を使う。
規約：d.hom は固定した始点 c から d.right への射。
使われ方：Kerodon §5.3.3（Tag 025W）、transport prism の二端点での値。 -/
lemma weightedNerveUnderEvaluation_at {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) (d : Under c) :
    lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex d)) (𝟙 (F.obj c)) ≫ weightedNerveUnderEvaluation F c =
      F.map d.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift F d.right := by
  rw [weightedNerveUnderEvaluation, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantProduct_at,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift_map, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift_baseMap]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
