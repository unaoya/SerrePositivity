module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGInvertingRoof
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofFunctorCorrespondence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientFixedHomRoof

/-! # 任意の反転関手による実屋根の評価

概要：元の実屋根を、任意標的の実屋根へ全単体を保って写す。
方針：標的 slice の後合成と実添字を固定する pullback 写像を接続する。
規約：定義と可換性には反転条件を要しない。使われ方：局所化の任意標的への延長。
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

/-- 任意の関手による、元の実屋根全体の標的への変換。 -/
def dgInvertingRoofFunctorMap (P : Set D) (x y : D) {Y : SSet.{max u v}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoof A D P x F (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFunctorMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x) _ F rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)

omit [Small.{u} D] in
/-- 元の実屋根の標的変換は、実分母を厳密に固定する。 -/
lemma dgInvertingRoofFunctorMap_projection (P : Set D) (x y : D)
    {Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) :
    dgInvertingRoofFunctorMap A D P x y F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFunctorMap_snd _ _ _ _ _

omit [Small.{u} D] in
/-- 元の実屋根の標的変換の実射側は、標的 slice の後合成。 -/
lemma dgInvertingRoofFunctorMap_target (P : Set D) (x y : D)
    {Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) :
    dgInvertingRoofFunctorMap A D P x y F ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFunctorMap_fst _ _ _ _ _

variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 元の恒等分母の固定 Hom の包含の実射側成分。 -/
lemma dgOriginalFixedHomRoofMap_target (P : Set D) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOriginalFixedHomRoofMap A D P x y ≫ pullback.fst _ _ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOriginalFixedHomRoofMap]
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso_hom_target,
    Iso.inv_hom_id_assoc]
  rfl

/-- 元の固定 Hom の包含も実恒等分母上にある。 -/
lemma dgOriginalFixedHomRoofMap_projection (P : Set D) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOriginalFixedHomRoofMap A D P x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOriginalFixedHomRoofMap]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]

/-- 任意標的への実屋根変換は、元の固定 Hom に対する関手の作用と厳密に可換。 -/
theorem dgInvertingRoofFunctorMap_fixedHom (P : Set D) (x y : D)
    {Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOriginalFixedHomRoofMap A D P x y ≫ dgInvertingRoofFunctorMap A D P x y F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, dgInvertingRoofFunctorMap_target, ← Category.assoc,
      dgOriginalFixedHomRoofMap_target, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap_pinched,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_target]
  · change _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F _ = _ ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x F _
    rw [Category.assoc, dgInvertingRoofFunctorMap_projection,
      dgOriginalFixedHomRoofMap_projection, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_projection, SSet.comp_const]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
