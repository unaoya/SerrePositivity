module
public import SerrePositivity.KST.SConstruction.MultiDiagonalAssembly

/-! # 反復の区間の両端から全零境界商への降下
概要：反復の一次方向の区間の両端は全零境界に入り、商では基点となる。
方針：零方向の自己射による固定点判定と cofiber の普遍性を使う。
規約：他の零方向の境界の処理は別に行う。使われ方：構造射の suspension への降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：定値の一次方向の単体の像は第零方向の零境界に属する。
方針：組み立ての添字の固定点の式を core の関手で写す。
規約：任意の内側の単体。使われ方：区間の全境界への所属。 -/
lemma multiDiagonalAssembly_constant_mem (r : ℕ) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (i : Fin 2)
    (x : ((oneDirectionRealizationFunctor r).obj X).obj d) :
    ((multiCoreSConstruction (r + 1) X).map
      (oneDirectionAssemblyIndex r d (SimplexCategory.const d.unop ⦋1⦌ i))).app d x ∈
        (zeroDirectionsRange {(0 : Fin (r + 1))} X).obj d := by
  apply (mem_zeroDirectionsRange_iff _ X d _).2
  rw [zeroDirectionsOperator_eq_map]
  change (((multiCoreSConstruction (r + 1) X).map
      (oneDirectionAssemblyIndex r d (SimplexCategory.const d.unop ⦋1⦌ i)) ≫
      (multiCoreSConstruction (r + 1) X).map
        (zeroDirectionsIndexEndomorphism {(0 : Fin (r + 1))} (fun _ => d))).app d) x = _
  rw [← CategoryTheory.Functor.map_comp, oneDirectionAssemblyIndex_constant_fixed]
  rfl

/-- 概要：区間の境界の組み立ての像は全零方向の境界に属する。
方針：区間境界の定値性と第零方向の像の有限合併への包含を使う。
規約：高次の退化境界も含む。使われ方：境界への制限の持ち上げ。 -/
lemma multiDiagonalAssembly_boundary_mem (r : ℕ) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ)
    (z : ((boundary 1).toSSet ⊗ (oneDirectionRealizationFunctor r).obj X).obj d) :
    (multiDiagonalAssembly r X).app d
      (((boundary 1).ι ▷ (oneDirectionRealizationFunctor r).obj X).app d z) ∈
        (zeroDirectionsFatBoundary (r + 1) X).obj d := by
  have hle : zeroDirectionsRange {(0 : Fin (r + 1))} X ≤
      zeroDirectionsFatBoundary (r + 1) X :=
    Finset.le_sup (f := fun j => zeroDirectionsRange (insert j ∅) X) (Finset.mem_univ 0)
  apply hle
  change ((multiCoreSConstruction (r + 1) X).map
    (oneDirectionAssemblyIndex r d (stdSimplex.objEquiv z.1.val))).app d z.2 ∈ _
  rw [intervalBoundary_simplex_constant z.1.val z.1.property]
  exact multiDiagonalAssembly_constant_mem r X d _ z.2

/-- 概要：区間の境界の組み立てを全零境界へ制限する。
方針：全単体での所属条件で部分複体へ持ち上げる。
規約：元の組み立ての射そのものを制限する。使われ方：cofiber の降下条件。 -/
def multiAssemblyBoundaryLift (r : ℕ) (X : StableModel.{u}) :
    (boundary 1).toSSet ⊗ (oneDirectionRealizationFunctor r).obj X ⟶
      (zeroDirectionsFatBoundary (r + 1) X : SSet.{u}) :=
  Subcomplex.lift (((boundary 1).ι ▷ (oneDirectionRealizationFunctor r).obj X) ≫
    multiDiagonalAssembly r X) (by
      intro d y hy
      obtain ⟨z, rfl⟩ := hy
      exact multiDiagonalAssembly_boundary_mem r X d z)

/-- 概要：境界への持ち上げを含めると元の区間境界の組み立てを回収する。
方針：部分複体の持ち上げの式。
規約：厳密等号。使われ方：商の基点条件。 -/
lemma multiAssemblyBoundaryLift_ι (r : ℕ) (X : StableModel.{u}) :
    multiAssemblyBoundaryLift r X ≫ (zeroDirectionsFatBoundary (r + 1) X).ι =
      ((boundary 1).ι ▷ (oneDirectionRealizationFunctor r).obj X) ≫
        multiDiagonalAssembly r X := Subcomplex.lift_ι _ _

/-- 概要：区間の全境界は全零境界商の基点へ写る。
方針：境界への制限と cofiber の関係式を合成する。
規約：全ての高次単体での等号。使われ方：区間商への降下。 -/
lemma multiDiagonalAssembly_boundary_condition (r : ℕ) (X : StableModel.{u}) :
    ((boundary 1).ι ▷ (oneDirectionRealizationFunctor r).obj X) ≫
        multiDiagonalAssembly r X ≫ boundaryReductionQuotient r X =
      toUnit ((boundary 1).toSSet ⊗ (oneDirectionRealizationFunctor r).obj X) ≫
        (boundaryReducedRealization r X).hom := by
  rw [← Category.assoc, ← multiAssemblyBoundaryLift_ι, Category.assoc]
  change _ ≫ ((zeroDirectionsFatBoundary (r + 1) X).ι ≫
    PointedObject.cofiberQuotient (zeroDirectionsFatBoundary (r + 1) X).ι) = _
  rw [PointedObject.cofiberQuotient_condition, comp_toUnit_assoc]
  rfl

/-- 概要：区間の両端全体を潰す商から全零境界商への点つき射。
方針：全境界が基点へ写る式を cofiber の普遍性に渡す。
規約：源はまだ reduced suspension ではない。使われ方：反復間の構造射の降下。 -/
def multiIntervalBoundaryComparison (r : ℕ) (X : StableModel.{u}) :
    PointedObject.cofiber ((boundary 1).ι ▷ (oneDirectionRealizationFunctor r).obj X) ⟶
      boundaryReducedRealization r X :=
  PointedObject.cofiberDesc _ _ (multiDiagonalAssembly r X ≫ boundaryReductionQuotient r X)
    (multiDiagonalAssembly_boundary_condition r X)

/-- 概要：区間商への射影は組み立ての全境界商への射を回収する。
方針：cofiber の普遍性の式。
規約：局所化前の厳密等号。使われ方：自然性と他の零方向の境界条件。 -/
lemma multiIntervalBoundaryComparison_quotient (r : ℕ) (X : StableModel.{u}) :
    PointedObject.cofiberQuotient ((boundary 1).ι ▷ (oneDirectionRealizationFunctor r).obj X) ≫
      (multiIntervalBoundaryComparison r X).right =
        multiDiagonalAssembly r X ≫ boundaryReductionQuotient r X :=
  PointedObject.cofiberQuotient_desc _ _ _ _

end SerrePositivity.KST.SConstruction
