module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.RoofPinchedSlicePostcomp
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceProjectionLaws

/-! # 任意の関手による標的 slice の変換

概要：標的の関手が実 slice に誘導する射を、端点輸送ごと構成する。
方針：点の後合成の自然性で端点を同定し、台の join 射で関手性を確認する。
規約：quasicategory 性や dg 表示は不要。使われ方：反転関手による屋根の全単体の評価。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 関手による頂点の点図式の後合成。 -/
lemma roofTargetPoint {X Y : SSet.{u}} (F : X ⟶ Y) (y : X _⦋0⦌) :
    SSet.yonedaEquiv.symm y ≫ F =
      SSet.yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) y) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- 関手による標的 slice の写像。 -/
def roofTargetSliceMap {X Y : SSet.{u}} (F : X ⟶ Y) (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm y) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp _ F ≫ (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (roofTargetPoint F y))).hom

/-- 標的 slice の写像の始域射影。 -/
lemma roofTargetSliceMap_projection {X Y : SSet.{u}} (F : X ⟶ Y) (y : X _⦋0⦌) :
    roofTargetSliceMap F y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ ≫ F := by
  dsimp only [roofTargetSliceMap]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverProjection_eqTransport,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection]
  exact roofTargetPoint F y

/-- 標的 slice の写像は、台の join 射の後合成である。 -/
lemma roofTargetSliceMap_val {X Y : SSet.{u}} (F : X ⟶ Y) (y : X _⦋0⦌)
    {n : SimplexCategoryᵒᵖ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm y)).obj n) :
    ((roofTargetSliceMap F y).app n s).val = s.val ≫ F := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.roofSliceTransport_val (roofTargetPoint F y) _

/-- 標的 slice の写像は恒等関手を厳密に保つ。 -/
lemma roofTargetSliceMap_id {X : SSet.{u}} (y : X _⦋0⦌) :
    roofTargetSliceMap (𝟙 X) y = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  rw [roofTargetSliceMap_val, Category.comp_id]
  rfl

/-- 標的 slice の写像は合成を全次数で厳密に保つ。 -/
lemma roofTargetSliceMap_comp {X Y Z : SSet.{u}} (F : X ⟶ Y) (G : Y ⟶ Z)
    (y : X _⦋0⦌) :
    roofTargetSliceMap F y ≫ roofTargetSliceMap G (F.app (Opposite.op ⦋0⦌) y) =
      roofTargetSliceMap (F ≫ G) y := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change ((roofTargetSliceMap G _).app n ((roofTargetSliceMap F y).app n s)).val = _
  rw [roofTargetSliceMap_val G, roofTargetSliceMap_val F]
  exact (Category.assoc s.val F G).trans (roofTargetSliceMap_val (F ≫ G) y s).symm

/-- 標的 slice の関手性は実 pinched Hom の後合成と厳密に両立する。 -/
lemma roofTargetSliceMap_pinched {X Y : SSet.{u}} (F : X ⟶ Y) (x y : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso x y).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)) x ≫
      roofTargetSliceMap F y =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso _ _).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
        (SSet.yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) y)))
        (F.app (Opposite.op ⦋0⦌) x) := by
  simpa only [roofTargetSliceMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso, Iso.refl_hom,
    Category.id_comp] using
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.roofPinchedSlice_postcomp F x y rfl rfl (roofTargetPoint F y)

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof
