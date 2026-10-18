module
public import SerrePositivity.KST.SConstruction.OneDirectionReduction

/-! # 一次方向を消す比較の全零境界商への降下
概要：S₁ の比較を残りの全零境界を潰した商へ降ろす。
方針：比較の境界への制限と cofiber の普遍性を使い、射影で自然性を検出する。
規約：商の射の弱同値性はまだ主張しない。使われ方：反復間の構造射の源の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：一次方向の比較を残りの全零境界へ制限する。
方針：比較が零境界の像を保つ条件で持ち上げる。
規約：反復数は正。使われ方：点つき商への降下条件。 -/
def oneDirectionComparisonBoundaryMap (r : ℕ) (X : StableModel.{u}) :
    (oneDirectionFatBoundary (r + 1) X : SSet.{u}) ⟶
      (zeroDirectionsFatBoundary (r + 1) X : SSet.{u}) :=
  Subcomplex.lift ((oneDirectionFatBoundary (r + 1) X).ι ≫
    oneDirectionRealizationComparison (r + 1) X) (by
      simpa only [Subcomplex.image_eq_range] using
        oneDirectionComparison_fatBoundary_image_le (r + 1) X)

/-- 概要：境界への制限を含めると元の一次方向の比較を回収する。
方針：部分複体への持ち上げの式。
規約：厳密等号。使われ方：商の基点条件。 -/
lemma oneDirectionComparisonBoundaryMap_ι (r : ℕ) (X : StableModel.{u}) :
    oneDirectionComparisonBoundaryMap r X ≫ (zeroDirectionsFatBoundary (r + 1) X).ι =
      (oneDirectionFatBoundary (r + 1) X).ι ≫ oneDirectionRealizationComparison (r + 1) X :=
  Subcomplex.lift_ι _ _

/-- 概要：一次方向を消す比較を残りの全零境界の商へ降ろす。
方針：境界への制限と標的の商の関係式を使う。
規約：弱同値性や自然な逆射は仮定しない。使われ方：構造射の源の点つき比較。 -/
def oneDirectionReducedComparison (r : ℕ) (X : StableModel.{u}) :
    oneDirectionReducedRealization r X ⟶ boundaryReducedRealization r X :=
  PointedObject.cofiberDesc _ _
    (oneDirectionRealizationComparison (r + 1) X ≫ boundaryReductionQuotient r X) (by
      rw [← Category.assoc, ← oneDirectionComparisonBoundaryMap_ι, Category.assoc]
      change _ ≫ ((zeroDirectionsFatBoundary (r + 1) X).ι ≫
        PointedObject.cofiberQuotient (zeroDirectionsFatBoundary (r + 1) X).ι) = _
      rw [PointedObject.cofiberQuotient_condition, comp_toUnit_assoc]
      rfl)

/-- 概要：商へ降ろした比較を元の実現に引き戻した式。
方針：cofiber の降下の関係式。
規約：全単体の等号。使われ方：自然性と局所化比較の検証。 -/
lemma oneDirectionReducedComparison_quotient (r : ℕ) (X : StableModel.{u}) :
    oneDirectionReductionQuotient r X ≫ (oneDirectionReducedComparison r X).right =
      oneDirectionRealizationComparison (r + 1) X ≫ boundaryReductionQuotient r X :=
  PointedObject.cofiberQuotient_desc _ _ _ _

/-- 概要：境界商上の一次方向の比較は入力の射と可換。
方針：商への射影で検出し、元の比較と各商の自然性を使う。
規約：全 cofiber 保存射。使われ方：自然な構造写像の比較図式。 -/
lemma oneDirectionReducedComparison_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (oneDirectionReducedRealizationFunctor r).map f ≫ oneDirectionReducedComparison r Y =
      oneDirectionReducedComparison r X ≫ (boundaryReducedRealizationFunctor r).map f := by
  apply PointedObject.cofiber_hom_ext (oneDirectionFatBoundary (r + 1) X).ι
  change oneDirectionReductionQuotient r X ≫ (oneDirectionReducedRealizationMap r f).right ≫
      (oneDirectionReducedComparison r Y).right =
    oneDirectionReductionQuotient r X ≫ (oneDirectionReducedComparison r X).right ≫ (boundaryReducedRealizationMap r f).right
  have hn := (oneDirectionRealizationComparisonNat (r + 1)).naturality f
  change (oneDirectionRealizationFunctor (r + 1)).map f ≫
      oneDirectionRealizationComparison (r + 1) Y =
    oneDirectionRealizationComparison (r + 1) X ≫ (multiRealizationFunctor (r + 1)).map f at hn
  rw [← Category.assoc, oneDirectionReducedRealizationMap_quotient, Category.assoc,
    oneDirectionReducedComparison_quotient, ← Category.assoc, hn, Category.assoc,
    ← boundaryReducedRealizationMap_quotient, ← Category.assoc, ← Category.assoc,
    oneDirectionReducedComparison_quotient]

/-- 概要：一次方向を消す境界商の比較を自然変換へまとめる。
方針：各入力に cofiber の比較を置く。
規約：厳密な点つき自然変換。使われ方：構造写像の源の自然な比較。 -/
def oneDirectionReducedComparisonNat (r : ℕ) :
    oneDirectionReducedRealizationFunctor r ⟶ boundaryReducedRealizationFunctor r where
  app := oneDirectionReducedComparison r
  naturality {_X _Y} f := oneDirectionReducedComparison_naturality r f

end SerrePositivity.KST.SConstruction
