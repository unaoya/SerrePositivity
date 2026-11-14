module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGActualRoofCoefficientTransport

/-! # 有限実屋根図式の一つの実閉分母による表示

概要：任意有限屋根図式を、一つの閉分母上の係数族と元の実屋根内の輸送で表示する。
方針：実 Verdier over の join 錐と右ファイブレーションの終端固定 prism を使う。
規約：通常の閉分母添字圏の filtered 性は仮定しない。
使われ方：有限係数の Ore 細分を実屋根図式へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {K : SSet.{max u v}}
variable (r : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y)

/-- 一つの実閉分母上の全係数と、元の実屋根図式への全輸送。 -/
structure DGFiniteRoofPresentation where
  denominator : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x
  coefficient : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) denominator.obj.left) y
  transport : SSet.Homotopy
    (coefficient ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y denominator) r

/-- 任意の有限実屋根図式は、一つの実閉分母上に全ホモトピー付きで表示できる。 -/
theorem dgFiniteRoofPresentation_nonempty [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] [K.Finite] :
    Nonempty (DGFiniteRoofPresentation A D P x y r) := by
  obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierFiniteJoinCone_nonempty A D
    (r ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y)
  obtain ⟨R⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofRelativeFiberReduction_of_cone
    (i := 𝟙 K) (p := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y)
    (q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y) (F := 𝟙 _) (a := r) (g := r)
    (Category.id_comp _) (by simp only [Category.id_comp, Category.comp_id]) c
  let d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverVertexClosed A D P x R.cone.vertex
  let f := R.boundary ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso A D P x y R.cone.vertex).hom
  have hd : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y d =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofHomInclusion A D P x y R.cone.vertex :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofHomInclusion_vertex_transport A D P x y
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverVertexClosed_vertex A D P x R.cone.vertex)
  have hf : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y d =
      R.boundary ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y) R.cone.vertex := by
    rw [hd]
    change (R.boundary ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso A D P x y R.cone.vertex).hom) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso A D P x y R.cone.vertex).inv ≫ _) = _
    rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact ⟨⟨d, f, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget R.boundaryTransport hf.symm rfl⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
