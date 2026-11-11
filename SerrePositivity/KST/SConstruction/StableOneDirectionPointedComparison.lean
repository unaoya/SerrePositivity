module
public import SerrePositivity.KST.SConstruction.StableOneDirectionReducedComparison
public import SerrePositivity.KST.SConstruction.PointedSSetWhisker
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.StrictSimplicialTransformation

/-!
概要：元の S₁ 商比較を全自然同値族に厳密に自然な点つき変換にする。
方針：元の基点固定族自然性を標準点つき Hom の前後合成へ包装する。
規約：同じ比較を保ち逆を選ばない。使われ方：有限 native 隣接段 span の構成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet InfinityCategories LocalizingInvariants

/-- 概要：同じ元の点つき S₁ 商比較。
方針：元の比較射を標準点つき対象間の射とする。
規約：比較の変更なし。使われ方：全族変換の成分。 -/
def stableOneDirectionPointedComparisonMap (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableOneDirectionPointedEnrichedFunctor r).obj C ⟶
      (stableBoundaryPointedEnrichedFunctor r).obj C :=
  oneDirectionReducedComparison r (stableCategoryModel C)

/-- 概要：元の点つき S₁ 比較は全 Hom の前後合成と可換。
方針：同じ全基点固定族の自然性を標準豊穣の式に直す。
規約：全高次入力を保持。使われ方：厳密自然変換の包装。 -/
lemma stableOneDirectionPointedComparison_whisker (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableOneDirectionPointedEnrichedFunctor r).map C D ≫
        eHomWhiskerLeft SSet ((stableOneDirectionPointedEnrichedFunctor r).obj C)
          (stableOneDirectionPointedComparisonMap r D) =
      (stableBoundaryPointedEnrichedFunctor r).map C D ≫
        eHomWhiskerRight SSet (stableOneDirectionPointedComparisonMap r C)
          ((stableBoundaryPointedEnrichedFunctor r).obj D) := by
  rw [pointedSSetObject_whiskerLeft, pointedSSetObject_whiskerRight]
  exact stableOneDirectionReducedComparison_family r C D

/-- 概要：全自然同値族に厳密に自然な、同じ元の S₁ 商比較。
方針：検証済みの全 Hom 可換式を束ねる。
規約：BF 関手を構成しない。使われ方：同じ Ex∞ 後の全図式比較。 -/
def stableOneDirectionPointedComparison (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (stableOneDirectionPointedEnrichedFunctor r) (stableBoundaryPointedEnrichedFunctor r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _ (stableOneDirectionPointedComparisonMap r)
    (stableOneDirectionPointedComparison_whisker r)

/-- 概要：変換の成分は元の同じ比較射。
方針：標準豊穣包装の成分を展開する。
規約：実射の回収。使われ方：元の隣接段構造との照合。 -/
lemma stableOneDirectionPointedComparison_app (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableOneDirectionPointedComparison r).app C =
      eHomEquiv SSet (stableOneDirectionPointedComparisonMap r C) := rfl

end SerrePositivity.KST.SConstruction
