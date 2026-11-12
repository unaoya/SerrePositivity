module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.DiagonalCocartesianSectionsReindex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportDiagonalSimplex

/-!
概要：通常圏の nerve 上の全 cocartesian fibrations を、実際の Cat∞ 値分類写像に束ねる。
方針：底の射列上の undercategory と元の fibration の coherent 単体を対角評価して curry する。
規約：全相対 Hom の core の同じ混合作用を使う。分類の同値性はまだ結論しない。
使われ方：Cat∞ 値 straightening の一般の通常圏の nerve 上の主写像。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 底の射列と cocartesian fibrations の coherent 単体を、同じ元の相対作用で対角評価する。 -/
def cocartesianStrictTransportDiagonalSimplex
    {C : Type u} [Category.{u} C] {n : ℕ} (σ : (nerve C) _⦋n⦌)
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve C)) _⦋n⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalCocartesianSectionsEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportSimplexUnderDiagram σ) F

/-- 同じ対角単体の両入力は、任意の面・退化で同時に自然に制限される。 -/
lemma cocartesianStrictTransportDiagonalSimplex_naturality
    {C : Type u} [Category.{u} C] {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (nerve C) _⦋n⦌) (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve C)) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.map α.op (cocartesianStrictTransportDiagonalSimplex σ F) =
      cocartesianStrictTransportDiagonalSimplex ((nerve C).map α.op σ)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve C)).map α.op F) := by
  change (SimplicialThickening.functor α.toOrderHom.uliftMap).comp SSet
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalCocartesianSectionsEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportSimplexUnderDiagram σ) F) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalCocartesianSectionsEvaluation
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportSimplexUnderDiagram ((nerve C).map α.op σ))
      ((SimplicialThickening.functor α.toOrderHom.uliftMap).comp SSet F)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalCocartesianSectionsEvaluation_reindex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictTransportSimplexUnderDiagram_reindex]

/-- 元の底と元の全 cocartesian fibrations を同時に動かす、Cat∞ 値の共同評価。 -/
def cocartesianStrictTransportJointEvaluation (C : Type u) [Category.{u} C] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⊗
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve C) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} where
  app _ := ↾fun s ↦ cocartesianStrictTransportDiagonalSimplex s.1.down s.2
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (cocartesianStrictTransportDiagonalSimplex_naturality α.unop s.1.down s.2).symm

/-- 元の全 cocartesian fibration と全相対 Hom に作用する、Cat∞ 値 straightening 写像。 -/
def cocartesianStraighteningCoherentMap (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve C) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) :=
  curry (cocartesianStrictTransportJointEvaluation C)

/-- 構成済みの同じ分類写像の共同評価は、同じ底と同じ全相対作用から作った共同評価となる。 -/
lemma cocartesianStraighteningCoherentMap_uncurry (C : Type u) [Category.{u} C] :
    uncurry (cocartesianStraighteningCoherentMap C) = cocartesianStrictTransportJointEvaluation C :=
  uncurry_curry _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
