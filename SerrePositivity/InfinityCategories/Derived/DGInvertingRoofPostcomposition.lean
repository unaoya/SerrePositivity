module
public import SerrePositivity.InfinityCategories.Derived.DGInvertingRoofFunctor

/-! # 任意標的の実屋根の後合成

概要：任意の標的関手による実屋根の変換は、固定 Hom と元の屋根の像を厳密に保つ。
方針：共通実分母上の pullback 写像と、その二射影を比較する。
規約：反転関手は合成後も反転関手。使われ方：商 Hom への延長の標的自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 標的の後合成による、同じ実分母上の屋根変換。 -/
def dgInvertingRoofPostcompMap (P : Set D) (x : D) {Y Z : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) (G : Y ⟶ Z) (z : Y _⦋0⦌) :
    dgInvertingRoof A D P x F z ⟶
      dgInvertingRoof A D P x (F ≫ G) (G.app (Opposite.op ⦋0⦌) z) :=
  roofFunctorMap (dgVerdierOverSource A D P x ≫ F)
    (dgVerdierOverSource A D P x ≫ (F ≫ G)) G (Category.assoc _ _ _) z

omit [Small.{u} D] in
/-- 後合成の屋根変換は実分母への射影を保つ。 -/
lemma dgInvertingRoofPostcompMap_projection (P : Set D) (x : D)
    {Y Z : SSet.{max u v}} (F : dgNerve A D ⟶ Y) (G : Y ⟶ Z) (z : Y _⦋0⦌) :
    dgInvertingRoofPostcompMap A D P x F G z ≫
      dgInvertingRoofProjection A D P x (F ≫ G) (G.app (Opposite.op ⦋0⦌) z) =
        dgInvertingRoofProjection A D P x F z :=
  roofFunctorMap_snd _ _ _ _ _

omit [Small.{u} D] in
/-- 後合成の屋根変換の実射側成分。 -/
lemma dgInvertingRoofPostcompMap_target (P : Set D) (x : D)
    {Y Z : SSet.{max u v}} (F : dgNerve A D ⟶ Y) (G : Y ⟶ Z) (z : Y _⦋0⦌) :
    dgInvertingRoofPostcompMap A D P x F G z ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ roofTargetSliceMap G z :=
  roofFunctorMap_fst _ _ _ _ _

omit [Small.{u} D] in
/-- 元の屋根の像は、標的での後合成と厳密に可換。 -/
lemma dgInvertingRoofFunctorMap_postcomp (P : Set D) (x y : D)
    {Y Z : SSet.{max u v}} (F : dgNerve A D ⟶ Y) (G : Y ⟶ Z) :
    dgInvertingRoofFunctorMap A D P x y F ≫ dgInvertingRoofPostcompMap A D P x F G
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) =
        dgInvertingRoofFunctorMap A D P x y (F ≫ G) :=
  roofFunctorMap_comp _ _ _ _ _ rfl (Category.assoc _ _ _) _

variable [IsDGPretriangulated A D]

/-- 任意標的の屋根の後合成は、固定 Hom の後合成と厳密に可換。 -/
theorem dgInvertingFixedHomRoofMap_postcomp (P : Set D) (x : D)
    {Y Z : SSet.{max u v}} (F : dgNerve A D ⟶ Y) (G : Y ⟶ Z) (z : Y _⦋0⦌) :
    dgInvertingFixedHomRoofMap A D P x F z ≫ dgInvertingRoofPostcompMap A D P x F G z =
      pinchedHomMap G (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x)) z ≫
        dgInvertingFixedHomRoofMap A D P x (F ≫ G) (G.app (Opposite.op ⦋0⦌) z) := by
  apply pullback.hom_ext
  · rw [Category.assoc, dgInvertingRoofPostcompMap_target, ← Category.assoc,
      dgInvertingFixedHomRoofMap_target, Category.assoc, roofTargetSliceMap_pinched,
      Category.assoc, dgInvertingFixedHomRoofMap_target]
    rfl
  · change _ ≫ dgInvertingRoofProjection A D P x (F ≫ G) _ = _ ≫
      dgInvertingRoofProjection A D P x (F ≫ G) _
    rw [Category.assoc, dgInvertingRoofPostcompMap_projection,
      dgInvertingFixedHomRoofMap_projection, Category.assoc,
      dgInvertingFixedHomRoofMap_projection, SSet.comp_const]

end SerrePositivity.InfinityCategories
