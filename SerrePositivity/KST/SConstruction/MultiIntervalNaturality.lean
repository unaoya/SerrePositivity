module
public import SerrePositivity.KST.SConstruction.MultiAssemblyBoundary

/-! # 反復の区間商から全零境界商への自然な比較
概要：区間両端を潰す商と、その全零境界商への写像を入力の関手としてまとめる。
方針：一般の区間商関手に一次方向の実現を代入し、射影で自然性を検出する。
規約：源を reduced suspension と同一視する工程は別。使われ方：構造写像の関手性。
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

/-- 概要：単体集合の区間の両端全体を一つの基点に潰す関手。
方針：定値の単体的図式の区間商を使う。
規約：元の単体集合に基点の選択は不要。使われ方：反復の構造射の源。 -/
def intervalBoundaryQuotientFunctor : SSet.{u} ⥤ PointedSimplicialSet.{u} :=
  Functor.const SimplexCategoryᵒᵖ ⋙ diagonalIntervalFunctor

/-- 概要：一次方向を固定した反復の実現の区間商の関手。
方針：実現の関手と区間商を合成する。
規約：選んだ零対象の保存を要求しない。使われ方：全零境界商への自然変換。 -/
def multiIntervalBoundaryFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u} :=
  oneDirectionRealizationFunctor r ⋙ intervalBoundaryQuotientFunctor

/-- 概要：区間商から全零境界商への比較は入力の射と可換。
方針：cofiber の射影で検出し、組み立てと商の自然性を使う。
規約：厳密な点つき射の等号。使われ方：構造写像の自然性。 -/
lemma multiIntervalBoundaryComparison_naturality (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (multiIntervalBoundaryFunctor r).map f ≫ multiIntervalBoundaryComparison r Y =
      multiIntervalBoundaryComparison r X ≫ (boundaryReducedRealizationFunctor r).map f := by
  apply PointedObject.cofiber_hom_ext
    ((boundary 1).ι ▷ (oneDirectionRealizationFunctor r).obj X)
  change _ ≫ (diagonalIntervalMap
      ((Functor.const SimplexCategoryᵒᵖ).map ((oneDirectionRealizationFunctor r).map f))).right ≫
        (multiIntervalBoundaryComparison r Y).right =
    _ ≫ (multiIntervalBoundaryComparison r X).right ≫ (boundaryReducedRealizationMap r f).right
  have hq := diagonalIntervalMap_quotient
    ((Functor.const SimplexCategoryᵒᵖ).map ((oneDirectionRealizationFunctor r).map f))
  change PointedObject.cofiberQuotient
      ((boundary 1).ι ▷ (oneDirectionRealizationFunctor r).obj X) ≫
      (diagonalIntervalMap
        ((Functor.const SimplexCategoryᵒᵖ).map ((oneDirectionRealizationFunctor r).map f))).right =
    ((Δ[1] : SSet.{u}) ◁ (oneDirectionRealizationFunctor r).map f) ≫
      PointedObject.cofiberQuotient
        ((boundary 1).ι ▷ (oneDirectionRealizationFunctor r).obj Y) at hq
  rw [← Category.assoc, hq, Category.assoc,
    multiIntervalBoundaryComparison_quotient, ← Category.assoc,
    multiDiagonalAssembly_naturality, Category.assoc,
    ← boundaryReducedRealizationMap_quotient, ← Category.assoc, ← Category.assoc,
    multiIntervalBoundaryComparison_quotient]

/-- 概要：区間両端を潰す商から全零境界商への自然変換。
方針：各入力に組み立ての降下を取る。
規約：全高次単体を含む厳密な自然性。使われ方：反復間の構造写像の比較図式。 -/
def multiIntervalBoundaryComparisonNat (r : ℕ) :
    multiIntervalBoundaryFunctor r ⟶ boundaryReducedRealizationFunctor r where
  app := multiIntervalBoundaryComparison r
  naturality {_X _Y} f := multiIntervalBoundaryComparison_naturality r f

end SerrePositivity.KST.SConstruction
