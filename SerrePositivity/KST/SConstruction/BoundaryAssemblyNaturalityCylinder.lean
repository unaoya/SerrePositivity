module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyNaturalityFamilies
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.DoubleMappingCylinderDesc

/-! # 随伴構造射の自然性の二重写像円筒
概要：延長側と逆射側の合成族を一つの実際のパラメーター空間へ貼る。
方針：共通の中間選択上の厳密等号を定数円筒として貼り付ける。
規約：円筒自体の Kan 性・可縮性を仮定しない。
使われ方：Kan 置換後の可縮な自然性パラメーター族。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping Comparison
open scoped Simplicial

/-- 二つの合成族の中間選択を円筒でつなぐパラメーター空間。 -/
def boundaryAssemblyNaturalityCylinder (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder (boundaryAssemblyExtensionMiddle r f) (boundaryAssemblyInverseMiddle r f)

/-- 二重円筒上へ厳密に貼り合わせた実際の写像空間の族。 -/
def boundaryAssemblyNaturalityCylinderFamily (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryAssemblyNaturalityCylinder r f ⟶
      (PointedObject.basedHom ((boundaryKanRealizationFunctor r).obj X)
        ((loopBoundaryKanFunctor (r + 1)).obj Y)).right :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderDesc (boundaryAssemblyExtensionMiddle r f) (boundaryAssemblyInverseMiddle r f)
    (fst _ (Δ[1] : SSet.{u}) ≫ boundaryAssemblyExtensionMiddle r f ≫
      boundaryAssemblyExtensionFamily r f)
    (boundaryAssemblyExtensionFamily r f) (boundaryAssemblyInverseFamily r f)
    (by simp) (by
      rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]
      exact boundaryAssemblyNaturalityFamilies_middle r f)

/-- 貼り合わせた族の左側への制限は元の延長側の族。 -/
lemma boundaryAssemblyNaturalityCylinderFamily_left (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left (boundaryAssemblyExtensionMiddle r f) (boundaryAssemblyInverseMiddle r f) ≫
      boundaryAssemblyNaturalityCylinderFamily r f = boundaryAssemblyExtensionFamily r f :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_desc ..

/-- 貼り合わせた族の右側への制限は元の逆射側の族。 -/
lemma boundaryAssemblyNaturalityCylinderFamily_right (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right (boundaryAssemblyExtensionMiddle r f) (boundaryAssemblyInverseMiddle r f) ≫
      boundaryAssemblyNaturalityCylinderFamily r f = boundaryAssemblyInverseFamily r f :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_desc ..

/-- 元の源の構造射の全パラメーターを円筒へ含める。 -/
def boundaryAssemblyNaturalityCylinderSource (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryKanAssemblyChoices r X ⟶ boundaryAssemblyNaturalityCylinder r f :=
  boundaryAssemblyExtensionSource r f ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left (boundaryAssemblyExtensionMiddle r f) (boundaryAssemblyInverseMiddle r f)

/-- 元の標的の構造射の全パラメーターを円筒へ含める。 -/
def boundaryAssemblyNaturalityCylinderTarget (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryKanAssemblyChoices r Y ⟶ boundaryAssemblyNaturalityCylinder r f :=
  boundaryAssemblyInverseTarget r f ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right (boundaryAssemblyExtensionMiddle r f) (boundaryAssemblyInverseMiddle r f)

/-- 円筒の族は源で元の随伴構造射の族の後合成を厳密に回収する。 -/
lemma boundaryAssemblyNaturalityCylinderFamily_source (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryAssemblyNaturalityCylinderSource r f ≫ boundaryAssemblyNaturalityCylinderFamily r f =
      boundaryKanAssemblyAdjointFamily r X ≫
        (PointedObject.basedHomMap ((boundaryKanRealizationFunctor r).obj X)
          ((loopBoundaryKanFunctor (r + 1)).map f)).right := by
  rw [boundaryAssemblyNaturalityCylinderSource, Category.assoc,
    boundaryAssemblyNaturalityCylinderFamily_left]
  exact boundaryAssemblyNaturalityFamilies_source r f

/-- 円筒の族は標的で元の随伴構造射の族の前合成を厳密に回収する。 -/
lemma boundaryAssemblyNaturalityCylinderFamily_target (r : ℕ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    boundaryAssemblyNaturalityCylinderTarget r f ≫ boundaryAssemblyNaturalityCylinderFamily r f =
      boundaryKanAssemblyAdjointFamily r Y ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((boundaryKanRealizationFunctor r).map f)
          ((loopBoundaryKanFunctor (r + 1)).obj Y)).right := by
  rw [boundaryAssemblyNaturalityCylinderTarget, Category.assoc,
    boundaryAssemblyNaturalityCylinderFamily_right]
  exact boundaryAssemblyNaturalityFamilies_target r f

end SerrePositivity.KST.SConstruction
