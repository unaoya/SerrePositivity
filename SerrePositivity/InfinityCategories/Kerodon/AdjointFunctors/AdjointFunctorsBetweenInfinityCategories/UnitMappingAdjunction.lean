module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitLeftTriangle
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：各点の標準単位比較の同値性から指定単位を持つ随伴を構成する。
方針：基底固定の comma 比較から余単位を選び、証明済みの左右三角恒等式を使う。
規約：各点の条件に全パラメータの同値条件を追加しない。
使われ方：Kerodon Corollary 6.2.6.5（Tag 02FX） の指定単位による随伴の判定。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
local instance unitMappingAdjunctionHomCategory (A B : SSet.QCat.{u}) : Category.{u} (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

/-- 概要：各点の標準単位比較がホモトピー同値なら、指定単位を持つ随伴を構成できる。
方針：同じ comma 比較から余単位と両三角恒等式を得て双圏の随伴へ戻す。
規約：単位の選択は変更しない。非定値パラメータに対する比較同値性は仮定しない。
使われ方：指定単位による写像空間判定の逆方向。 -/
noncomputable def qcatAdjunctionOfUnitMappingSpaceCondition
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G := by
  let c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaCounitData η := Classical.choice hη.nonempty_counitData
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.mkOfHomTriangles
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 X) (F ≫ G)).symm η)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (G ≫ F) (𝟙 Y)).symm c.counitHom) ?_ ?_
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatLeftZigzag_hom]
    simp only [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
      eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp]
    exact (hη.left_triangle c).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X Y).map_id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F)).symm
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatRightZigzag_hom]
    simp only [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
      eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp]
    exact c.right_triangle.trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor Y X).map_id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G)).symm

/-- 概要：各点の条件から構成した随伴の単位は指定された η。
方針：二胞体の表示同値の両逆を使う。
規約：同型を介さない h Fun の射の等式。
使われ方：指定単位を持つ随伴の存在判定。 -/
lemma qcatAdjunctionOfUnitMappingSpaceCondition_unitHom
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) :
    (qcatAdjunctionOfUnitMappingSpaceCondition η hη).unitHom = η :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 X) (F ≫ G)).apply_symm_apply η

/-- 概要：指定単位を持つ随伴の存在は各点の標準単位比較の同値性と同値。
方針：順方向は随伴の標準比較、逆方向は comma 比較と三角恒等式の構成。
規約：標準比較そのものの同値性を使い、任意の各点の同値へは弱めない。
使われ方：Kerodon Corollary 6.2.6.5（Tag 02FX） の局所存在判定。 -/
@[kerodon 02FX]
lemma qcat_exists_adjunction_unitHom_iff_unitMappingSpaceCondition
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) :
    (∃ a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G, a.unitHom = η) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.unitMappingSpaceCondition
  · intro hη
    exact ⟨qcatAdjunctionOfUnitMappingSpaceCondition η hη,
      qcatAdjunctionOfUnitMappingSpaceCondition_unitHom η hη⟩

/-- 概要：各点の標準単位比較条件から非定値関手を含む全パラメータの Hom 全単射が従う。
方針：指定単位を持つ随伴を構成し、随伴の単位 Hom 判定へ戻す。
規約：全パラメータの条件は帰結であり、追加仮定ではない。
使われ方：局所判定と以前の全パラメータ版の判定の接続。 -/
lemma UnitMappingSpaceCondition.qcatUnitHomMap_bijective
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)}
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) {A : SSet.{u}} [Quasicategory A]
    (U : A ⟶ X) (V : A ⟶ Y) : Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap η U V) := by
  have h := (qcat_exists_adjunction_unitHom_iff_unitMappingSpaceCondition η).mpr hη
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcat_exists_adjunction_unitHom_iff η).mp h U V

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.2.2.8"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcat_exists_adjunction_unitHom_iff_unitMappingSpaceCondition
