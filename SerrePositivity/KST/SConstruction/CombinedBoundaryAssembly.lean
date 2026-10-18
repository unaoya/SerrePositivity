module
public import SerrePositivity.KST.SConstruction.OneDirectionBoundary

/-! # 区間の両端と零境界 cylinder を合わせた商
概要：両端と残りの全零方向の cylinder を同時に潰し、全反復の境界商へ写す。
方針：二つの部分複体の合併の像の所属を示し、cofiber の普遍性で降ろす。
規約：円の smash との同一視は別工程。使われ方：反復間の suspension 構造射の源。
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

/-- 概要：区間の両端と残りの零境界の cylinder の合併。
方針：第一射影と第二射影による逆像の上限を取る。
規約：部分複体として全高次単体を保持する。使われ方：同時 collapse の源。 -/
def combinedIntervalBoundary (r : ℕ) (X : StableModel.{u}) :
    ((Δ[1] : SSet.{u}) ⊗ (oneDirectionRealizationFunctor r).obj X).Subcomplex :=
  (boundary 1).preimage (fst (Δ[1] : SSet.{u}) ((oneDirectionRealizationFunctor r).obj X)) ⊔
    (oneDirectionFatBoundary r X).preimage
      (snd (Δ[1] : SSet.{u}) ((oneDirectionRealizationFunctor r).obj X))

/-- 概要：両端と零境界 cylinder の合併の像は標的の全零境界に属する。
方針：両端と残りの方向についての既存の所属判定を使う。
規約：全区間パラメーターと全高次単体。使われ方：商への降下条件。 -/
lemma combinedIntervalBoundary_image_le (r : ℕ) (X : StableModel.{u}) :
    (combinedIntervalBoundary r X).image (multiDiagonalAssembly r X) ≤
      zeroDirectionsFatBoundary (r + 1) X := by
  rw [Subcomplex.image_le_iff]
  intro d z hz
  change z.1 ∈ (boundary 1).obj d ∨ z.2 ∈ (oneDirectionFatBoundary r X).obj d at hz
  rcases hz with ha | hx
  · exact multiDiagonalAssembly_boundary_mem r X d (⟨z.1, ha⟩, z.2)
  · exact multiDiagonalAssembly_fatBoundary_mem r X d z.1 z.2 hx

/-- 概要：両端と零境界 cylinder の合併の像を標的の境界へ制限する。
方針：像の包含を部分複体への持ち上げへ渡す。
規約：元の組み立ての制限。使われ方：cofiber の基点条件。 -/
def combinedAssemblyBoundaryLift (r : ℕ) (X : StableModel.{u}) :
    (combinedIntervalBoundary r X : SSet.{u}) ⟶
      (zeroDirectionsFatBoundary (r + 1) X : SSet.{u}) :=
  Subcomplex.lift ((combinedIntervalBoundary r X).ι ≫ multiDiagonalAssembly r X) (by
    simpa only [Subcomplex.image_eq_range] using combinedIntervalBoundary_image_le r X)

/-- 概要：合併境界への制限を含めると元の組み立てを回収する。
方針：部分複体の持ち上げの式。
規約：厳密等号。使われ方：同時商の関係式。 -/
lemma combinedAssemblyBoundaryLift_ι (r : ℕ) (X : StableModel.{u}) :
    combinedAssemblyBoundaryLift r X ≫ (zeroDirectionsFatBoundary (r + 1) X).ι =
      (combinedIntervalBoundary r X).ι ≫ multiDiagonalAssembly r X := Subcomplex.lift_ι _ _

/-- 概要：両端と零境界 cylinder の全体は標的の商の基点へ写る。
方針：境界への制限と標的の cofiber の関係式を合成する。
規約：合併全体の一つの式。使われ方：同時商からの点つき写像。 -/
lemma combinedIntervalBoundary_condition (r : ℕ) (X : StableModel.{u}) :
    (combinedIntervalBoundary r X).ι ≫ multiDiagonalAssembly r X ≫
        boundaryReductionQuotient r X =
      toUnit (combinedIntervalBoundary r X : SSet.{u}) ≫
        (boundaryReducedRealization r X).hom := by
  rw [← Category.assoc, ← combinedAssemblyBoundaryLift_ι, Category.assoc]
  change _ ≫ ((zeroDirectionsFatBoundary (r + 1) X).ι ≫
    PointedObject.cofiberQuotient (zeroDirectionsFatBoundary (r + 1) X).ι) = _
  rw [PointedObject.cofiberQuotient_condition, comp_toUnit_assoc]
  rfl

/-- 概要：両端と残りの零境界 cylinder を同時に潰す点つき商。
方針：合併部分複体の包含の cofiber を取る。
規約：源の円の smash 表示は後で比較する。使われ方：反復間の構造射の源。 -/
def combinedIntervalQuotient (r : ℕ) (X : StableModel.{u}) : PointedSimplicialSet.{u} :=
  PointedObject.cofiber (combinedIntervalBoundary r X).ι

/-- 概要：両端と零境界 cylinder の同時商から全反復の全零境界商への射。
方針：組み立てが合併境界を基点へ送る式で cofiber から降ろす。
規約：追加の Kan 性・可縮性を仮定しない。使われ方：suspension 構造射の基本写像。 -/
def combinedIntervalAssembly (r : ℕ) (X : StableModel.{u}) :
    combinedIntervalQuotient r X ⟶ boundaryReducedRealization r X :=
  PointedObject.cofiberDesc _ _ (multiDiagonalAssembly r X ≫ boundaryReductionQuotient r X)
    (combinedIntervalBoundary_condition r X)

/-- 概要：同時商の射影は元の区間の組み立てを回収する。
方針：cofiber の降下の式。
規約：局所化前の厳密等号。使われ方：自然性と smash 表示との比較。 -/
lemma combinedIntervalAssembly_quotient (r : ℕ) (X : StableModel.{u}) :
    PointedObject.cofiberQuotient (combinedIntervalBoundary r X).ι ≫
      (combinedIntervalAssembly r X).right =
        multiDiagonalAssembly r X ≫ boundaryReductionQuotient r X :=
  PointedObject.cofiberQuotient_desc _ _ _ _

end SerrePositivity.KST.SConstruction
