module
public import SerrePositivity.KST.SConstruction.RawCofiberTensorDesc
public import SerrePositivity.KST.SConstruction.OneDirectionWeakComparison
public import SerrePositivity.KST.SConstruction.CombinedBoundaryAssembly

/-! # 反復 S の境界商への suspension からの射
概要：一次方向を固定した境界商の reduced suspension から、次の反復の境界商へ写す。
方針：区間の両端と零境界 cylinder の零化を、二つの cofiber の smash の降下へ渡す。
規約：源は S₁ 比較の源の模型。使われ方：反復間の構造写像の比較図式。
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

/-- 概要：残りの全零境界の cylinder の組み立てを標的の全零境界へ制限する。
方針：各単体の所属を部分複体への持ち上げへ渡す。
規約：区間の全体に適用する。使われ方：smash の右境界の降下条件。 -/
def zeroCylinderAssemblyLift (r : ℕ) (X : StableModel.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (oneDirectionFatBoundary r X : SSet.{u}) ⟶
      (zeroDirectionsFatBoundary (r + 1) X : SSet.{u}) :=
  Subcomplex.lift (((Δ[1] : SSet.{u}) ◁ (oneDirectionFatBoundary r X).ι) ≫
    multiDiagonalAssembly r X) (by
      intro d y hy
      obtain ⟨z, rfl⟩ := hy
      exact multiDiagonalAssembly_fatBoundary_mem r X d z.1 z.2.val z.2.property)

/-- 概要：零境界 cylinder の制限を含めると元の組み立てを回収する。
方針：部分複体への持ち上げの式。
規約：厳密等号。使われ方：商の基点条件。 -/
lemma zeroCylinderAssemblyLift_ι (r : ℕ) (X : StableModel.{u}) :
    zeroCylinderAssemblyLift r X ≫ (zeroDirectionsFatBoundary (r + 1) X).ι =
      ((Δ[1] : SSet.{u}) ◁ (oneDirectionFatBoundary r X).ι) ≫ multiDiagonalAssembly r X :=
  Subcomplex.lift_ι _ _

/-- 概要：残りの全零境界の cylinder は標的の全零境界商の基点へ写る。
方針：零境界への制限と標的の cofiber の関係式を合成する。
規約：全区間パラメーター・全次数の等号。使われ方：右 cofiber の降下。 -/
lemma multiDiagonalAssembly_zeroCylinder_condition (r : ℕ) (X : StableModel.{u}) :
    ((Δ[1] : SSet.{u}) ◁ (oneDirectionFatBoundary r X).ι) ≫
        multiDiagonalAssembly r X ≫ boundaryReductionQuotient r X =
      toUnit ((Δ[1] : SSet.{u}) ⊗ (oneDirectionFatBoundary r X : SSet.{u})) ≫
        (boundaryReducedRealization r X).hom := by
  rw [← Category.assoc, ← zeroCylinderAssemblyLift_ι, Category.assoc]
  change _ ≫ ((zeroDirectionsFatBoundary (r + 1) X).ι ≫
    PointedObject.cofiberQuotient (zeroDirectionsFatBoundary (r + 1) X).ι) = _
  rw [PointedObject.cofiberQuotient_condition, comp_toUnit_assoc]
  rfl

/-- 概要：一次方向の境界商の reduced suspension から次の反復の境界商への写像。
方針：区間の両端と零境界 cylinder の条件を二つの cofiber の smash の降下へ渡す。
規約：L9 の円と suspension の定義そのものを使う。使われ方：反復間の構造射の比較。
-/
def oneDirectionSuspensionAssembly (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (oneDirectionReducedRealization r X) ⟶ boundaryReducedRealization (r + 1) X :=
  rawCofiberTensorDesc (boundary.{u} 1).ι (oneDirectionFatBoundary (r + 1) X).ι
    (boundaryReducedRealization (r + 1) X)
    (multiDiagonalAssembly (r + 1) X ≫ boundaryReductionQuotient (r + 1) X)
    (multiDiagonalAssembly_boundary_condition (r + 1) X)
    (multiDiagonalAssembly_zeroCylinder_condition (r + 1) X)

/-- 概要：自由な基点を加えた cylinder から suspension への二つの商写像。
方針：区間の境界商と零境界商の射影を tensor する。
規約：源と標的の宇宙を明示する。使われ方：構造射の回収式。 -/
def oneDirectionSuspensionProjection (r : ℕ) (X : StableModel.{u}) :
    PointedObject.adjoin (Δ[1] : SSet.{u}) ⊗
      PointedObject.adjoin ((oneDirectionRealizationFunctor (r + 1)).obj X) ⟶
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (oneDirectionReducedRealization r X) :=
  PointedObject.cofiberProjection (boundary.{u} 1).ι ⊗ₘ
    PointedObject.cofiberProjection (oneDirectionFatBoundary (r + 1) X).ι

/-- 概要：二つの商写像で suspension の射を元の cylinder 上の射へ戻す。
方針：二段の cofiber の降下の回収式。
規約：自由な基点を加えた入力上の厳密等号。使われ方：構造射の比較と自然性。
-/
lemma oneDirectionSuspensionAssembly_quotient (r : ℕ) (X : StableModel.{u}) :
    oneDirectionSuspensionProjection r X ≫ oneDirectionSuspensionAssembly r X =
      adjoinTensorMap (boundaryReducedRealization (r + 1) X)
        (multiDiagonalAssembly (r + 1) X ≫ boundaryReductionQuotient (r + 1) X) :=
  rawCofiberTensorDesc_quotient (boundary.{u} 1).ι (oneDirectionFatBoundary (r + 1) X).ι
    (boundaryReducedRealization (r + 1) X)
    (multiDiagonalAssembly (r + 1) X ≫ boundaryReductionQuotient (r + 1) X)
    (multiDiagonalAssembly_boundary_condition (r + 1) X)
    (multiDiagonalAssembly_zeroCylinder_condition (r + 1) X)

end SerrePositivity.KST.SConstruction
