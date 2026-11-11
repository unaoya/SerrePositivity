module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingRoofFunctor

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 標的の後合成による、同じ実分母上の屋根変換。 -/
def dgInvertingRoofPostcompMap (P : Set D) (x : D) {Y Z : SSet.{max u v}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (G : Y ⟶ Z) (z : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoof A D P x F z ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoof A D P x (F ≫ G) (G.app (Opposite.op ⦋0⦌) z) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFunctorMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ (F ≫ G)) G (Category.assoc _ _ _) z

omit [Small.{u} D] in
/-- 後合成の屋根変換は実分母への射影を保つ。 -/
lemma dgInvertingRoofPostcompMap_projection (P : Set D) (x : D)
    {Y Z : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (G : Y ⟶ Z) (z : Y _⦋0⦌) :
    dgInvertingRoofPostcompMap A D P x F G z ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x (F ≫ G) (G.app (Opposite.op ⦋0⦌) z) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F z :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFunctorMap_snd _ _ _ _ _

omit [Small.{u} D] in
/-- 後合成の屋根変換の実射側成分。 -/
lemma dgInvertingRoofPostcompMap_target (P : Set D) (x : D)
    {Y Z : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (G : Y ⟶ Z) (z : Y _⦋0⦌) :
    dgInvertingRoofPostcompMap A D P x F G z ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap G z :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFunctorMap_fst _ _ _ _ _

omit [Small.{u} D] in
/-- 元の屋根の像は、標的での後合成と厳密に可換。 -/
lemma dgInvertingRoofFunctorMap_postcomp (P : Set D) (x y : D)
    {Y Z : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (G : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F ≫ dgInvertingRoofPostcompMap A D P x F G
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y (F ≫ G) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFunctorMap_comp _ _ _ _ _ rfl (Category.assoc _ _ _) _

variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 任意標的の屋根の後合成は、固定 Hom の後合成と厳密に可換。 -/
theorem dgInvertingFixedHomRoofMap_postcomp (P : Set D) (x : D)
    {Y Z : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (G : Y ⟶ Z) (z : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F z ≫ dgInvertingRoofPostcompMap A D P x F G z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap G (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) z ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x (F ≫ G) (G.app (Opposite.op ⦋0⦌) z) := by
  apply pullback.hom_ext
  · rw [Category.assoc, dgInvertingRoofPostcompMap_target, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_target, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap_pinched,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_target]
    rfl
  · change _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x (F ≫ G) _ = _ ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x (F ≫ G) _
    rw [Category.assoc, dgInvertingRoofPostcompMap_projection,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_projection, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_projection, SSet.comp_const]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
