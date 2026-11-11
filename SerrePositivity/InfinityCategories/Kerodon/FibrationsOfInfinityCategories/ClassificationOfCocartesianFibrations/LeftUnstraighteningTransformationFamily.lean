module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorParameterizedPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorParameterizedPrismNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFatDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraightening

/-!
概要：二つの coherent な空間値図式の変換の空間と、その全体をパラメーターとする評価。
方針：関手空間の両端固定の区間模型を用い、普遍的な変換の族を評価する。
規約：変換は可逆とは限らず、変換間の高次の比較を Kan 複体に保持する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な変換の写像空間と unstraightening の相対写像空間の接続。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：二つの coherent な図式の変換の空間を両端固定の区間模型で表す。
方針：関手単体集合の二つの関手頂点の間の区間写像空間を取る。
規約：底 B は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、unstraightening による変換の空間全体への作用の始域。 -/
def leftUnstraighteningTransformationSpace {B : SSet.{u + 1}} (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    SSet.{u + 1} := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)

/-- 概要：coherent な図式の変換の空間は Kan 複体。
方針：関手単体集合の quasicategory 性と、両端固定の区間模型の Kan 性を使う。
規約：底 B の quasicategory 性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、変換間の高次の可逆な比較の空間。 -/
instance leftUnstraighteningTransformationSpace_kanComplex {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) : KanComplex (leftUnstraighteningTransformationSpace F G) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace_kanComplex _ _

/-- 概要：coherent な変換の空間全体をパラメーターとする図式の評価。
方針：区間模型の普遍的な族を、追加パラメーター付き prism として評価する。
規約：定義域は (Δ¹ ⊗ B) と変換の空間の直積。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、変換を一本ずつではなく全体で持ち上げる底の族。 -/
def leftUnstraighteningTransformationFamily {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    ((Δ[1] : SSet.{u + 1}) ⊗ B) ⊗ leftUnstraighteningTransformationSpace F G ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 (leftUnstraighteningTransformationSpace F G)))

/-- 概要：変換の空間全体の評価の始点は元の図式 F に定値。
方針：区間模型の始点条件を追加パラメーター付き評価へ移す。
規約：変換の空間の因子を射影で忘れる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、普遍的な変換の族の始点の固定。 -/
lemma leftUnstraighteningTransformationFamily_zero {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex 1 0 B ▷ leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningTransformationFamily F G =
        fst B (leftUnstraighteningTransformationSpace F G) ≫ F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism_vertex_of_const 1 _ 0 F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_zero (𝟙 _))

/-- 概要：変換の空間全体の評価の終点は標的の図式 G に定値。
方針：区間模型の終点条件を追加パラメーター付き評価へ移す。
規約：変換の空間の因子を射影で忘れる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、普遍的な変換の族の終点の固定。 -/
lemma leftUnstraighteningTransformationFamily_one {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex 1 1 B ▷ leftUnstraighteningTransformationSpace F G) ≫
      leftUnstraighteningTransformationFamily F G =
        fst B (leftUnstraighteningTransformationSpace F G) ≫ G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism_vertex_of_const 1 _ 1 G (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_one (𝟙 _))

/-- 概要：普遍的な変換のパラメーター制限は指定した変換の族の評価。
方針：prism のパラメーター自然性と区間模型の uncurry を使う。
規約：パラメーターは任意。
使われ方：任意の族の底を普遍的な lift の底と同一視する。 -/
lemma leftUnstraighteningTransformationFamily_parameter {B K : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (t : K ⟶ leftUnstraighteningTransformationSpace F G) :
    ((Δ[1] ⊗ B) ◁ t) ≫ leftUnstraighteningTransformationFamily F G =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry t) := by
  rw [leftUnstraighteningTransformationFamily, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism_parameter,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, Category.comp_id]


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
