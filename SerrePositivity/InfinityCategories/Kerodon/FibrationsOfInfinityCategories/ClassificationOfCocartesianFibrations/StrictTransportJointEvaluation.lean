module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.DiagonalRelativeReindex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportDiagonalSimplex

/-!
概要：底と fibration の coherent パラメーターを同時に動かす strict transport の評価写像。
方針：対角評価の添字変換則により直積の各単体を 𝒮 の単体へ写す。
規約：底の nerve を u+1 に持ち上げ、二つの入力を同じ宇宙に置く。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類関手を curry する前の二変数の評価。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：strict transport の対角単体は二つの入力を同時に面・退化で制限する操作と可換。
方針：対角相対評価の添字変換と undercategory の図式の添字変換を合成する。
規約：任意の単体圏の射 α を許す。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、二変数の評価写像の単体的自然性。 -/
lemma strictTransportDiagonalSimplex_naturality
    {C : Type u} [Category.{u} C] {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (nerve C) _⦋n⦌) (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (nerve C)) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.map α.op (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportDiagonalSimplex σ F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportDiagonalSimplex ((nerve C).map α.op σ)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (nerve C)).map α.op F) := by
  change (SimplicialThickening.functor α.toOrderHom.uliftMap).comp SSet
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportSimplexUnderDiagram σ) F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportSimplexUnderDiagram ((nerve C).map α.op σ))
        ((SimplicialThickening.functor α.toOrderHom.uliftMap).comp SSet F)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeEvaluation_reindex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportSimplexUnderDiagram_reindex]

/-- 概要：底の nerve と left fibrations の ∞ 圏の直積から 𝒮 への strict transport の共同評価。
方針：同じ次数の射列と coherent な fibration の図式を対角評価し、添字変換の整合性を使う。
規約：定義域の左因子は持ち上げた底の nerve、右因子は fibration のパラメーター。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な straightening 関手の評価写像。 -/
noncomputable def strictTransportJointEvaluation (C : Type u) [Category.{u} C] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (nerve C) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} where
  app _ := ↾fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportDiagonalSimplex s.1.down s.2
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (strictTransportDiagonalSimplex_naturality α.unop s.1.down s.2).symm

/-- 概要：left fibrations の ∞ 圏から 𝒮 値の関手 ∞ 圏への coherent な strict transport 関手。
方針：二変数の評価を curry し、fibration の全ての高次パラメーターに作用させる。
規約：この段階では分類の同値性を結論に含めない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、通常の底の圏に対する straightening の構成方向。 -/
noncomputable def leftStraighteningCoherentMap (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (nerve C) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) :=
  curry (strictTransportJointEvaluation C)

/-- 概要：coherent な strict transport 関手を評価すると二変数の共同評価を回収する。
方針：curry と uncurry の往復の法則を使う。
規約：内部 Hom の定義域は持ち上げた底の nerve。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類関手の値と射の計算の出発点。 -/
lemma leftStraighteningCoherentMap_uncurry (C : Type u) [Category.{u} C] :
    uncurry (leftStraighteningCoherentMap C) = strictTransportJointEvaluation C :=
  uncurry_curry _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
