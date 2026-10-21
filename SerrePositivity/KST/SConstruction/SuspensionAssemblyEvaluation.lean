module
public import SerrePositivity.KST.SConstruction.SuspensionAssembly
public import SerrePositivity.KST.SConstruction.RawCofiberTensorEvaluation

/-! # 元の二つの商射上での suspension 組み立て
概要：元の区間と一次方向実現から、同じ suspension 組み立てを回収する。
方針：両境界を潰す降下の基礎射の評価をそのまま適用する。
規約：商も構造射も変更しない。使われ方：全 native 入力族との厳密可換性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories

/-- 元の二つの商射から、元の区間組み立てと標的の同じ商射を厳密に回収する。 -/
lemma oneDirectionSuspensionAssembly_underlying (r : ℕ) (X : StableModel.{u}) :
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ oneDirectionReductionQuotient r X) ≫
      PointedSimplicialSet.productToSmash PointedSimplicialSet.circle
        (oneDirectionReducedRealization r X) ≫ (oneDirectionSuspensionAssembly r X).right =
      multiDiagonalAssembly (r + 1) X ≫ boundaryReductionQuotient (r + 1) X :=
  rawCofiberTensorDesc_underlying (boundary.{u} 1).ι (oneDirectionFatBoundary (r + 1) X).ι
    (boundaryReducedRealization (r + 1) X)
    (multiDiagonalAssembly (r + 1) X ≫ boundaryReductionQuotient (r + 1) X)
    (multiDiagonalAssembly_boundary_condition (r + 1) X)
    (multiDiagonalAssembly_zeroCylinder_condition (r + 1) X)

end SerrePositivity.KST.SConstruction
