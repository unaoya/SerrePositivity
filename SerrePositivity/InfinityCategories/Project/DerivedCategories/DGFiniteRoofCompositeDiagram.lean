module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofOreData
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHomComposition

/-! # 有限実屋根 Ore データからの合成分子族と実屋根図式

概要：同時 Ore 細分の持ち上げ族と第二分子族を合成し、一つの実閉分母上の実図式に戻す。
方針：全次元 AW 合成と実閉分母の合成閉性を使う。
規約：指定入力との四三角形の高次比較は別工程。
使われ方：全関手圏への組み立てに必要な実屋根合成の候補図式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y z : D) {K : SSet.{max u v}}
variable {r : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y}
variable {s : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P y z}
variable (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofOreData A D P x y z r s)

/-- 細分持ち上げ族と第二分子族の全次元合成。 -/
def DGFiniteRoofOreData.compositeNumerator :
    K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D R.ore.refinedSource z :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily R.ore.lift R.second.coefficient

variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 二段 Ore 細分と第一入力の分母を合成した実閉分母。 -/
def DGFiniteRoofOreData.compositeDenominator : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x :=
  ⟨Over.mk (R.ore.combinedDenominator ≫ R.first.denominator.obj.hom),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_comp A D P R.ore.combinedDenominator
      R.first.denominator.obj.hom R.ore.combinedDenominator_mem R.first.denominator.property⟩

/-- 同時 Ore データから構成した、元の実屋根全空間への合成候補図式。 -/
def DGFiniteRoofOreData.compositeDiagram : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x z :=
  R.compositeNumerator ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x z R.compositeDenominator

/-- 合成候補図式の実分母射影は、構成した一つの合成分母に厳密に定値。 -/
lemma DGFiniteRoofOreData.compositeDiagram_projection :
    R.compositeDiagram ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x z =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x R.compositeDenominator) := by
  rw [DGFiniteRoofOreData.compositeDiagram, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion_projection, SSet.comp_const]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
