module
public import SerrePositivity.KST.SConstruction.SmallDGNativeSimplicialCategory

/-! # 小さい厳密 dg 入力の coherent nerve
概要：元の native Kan 写像空間を持つ実単体的圏に γ1 を適用して入力 ∞ 圏を得る。
方針：元の全 Hom の Kan 性と既存の coherent nerve の内角充填定理を使う。
規約：準同値や Morita 同値による局所化は施さない。使われ方：Sp 値 K の源。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の厳密 dg 関手と全 native Kan 関手族を保つ、小さい dg 入力の coherent nerve。 -/
def smallDGNativeNerve : SSet.{max (u + 1) (v + 1)} :=
  SimplicialNerve (SmallBundledDGCategory.{u, v} A)

/-- 元の全 native Kan 写像空間から得た小さい厳密 dg 入力の nerve は ∞ 圏。 -/
instance smallDGNativeNerve_quasicategory : Quasicategory (smallDGNativeNerve.{u, v} A) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory (SmallBundledDGCategory.{u, v} A)

end SerrePositivity.KST.SConstruction
