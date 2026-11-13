module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ThreeArrowGraphWeakComparison
public import SerrePositivity.EInfinity.BarrattEccles.HammockGraphColimit

/-!
# 任意可換環の元の Map^h と全語の hammock graph の弱比較

概要：元の三列の包含と元の Map^h の共通始域からの右射は弱ホモトピー同値となる。
方針：実際の E 代数のモデルと同じ指定分解を一般の比較へ代入する。
規約：環の標数や始域の cofibrancy を追加しない。既存 DK Hom への接続は後続。
使われ方：元の Kan Map^h と reduced hammock の高次比較。
-/

@[expose] public section
universe u
noncomputable section
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A]

lemma algebraHammockGraphInclusion_threeArrow_isWeakHomotopyEquivalence
    (X Y : (operad A).Algebra) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (algebraHammockGraphInclusion A _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow X Y) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.threeArrowGraphInclusion_isWeakHomotopyEquivalence X Y
    (mappingCofibrantFactorization A)

lemma mappingSpaceHammockColimitNerveMap_isWeakHomotopyEquivalence
    (X Y : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (mappingSpaceHammockColimitNerveMap A X Y) :=
  (mappingSpaceHammockGraphNerveMap_isWeakHomotopyEquivalence A X Y).comp
    (algebraHammockGraphInclusion_threeArrow_isWeakHomotopyEquivalence A X Y)

end SerrePositivity.EInfinity.BarrattEccles
