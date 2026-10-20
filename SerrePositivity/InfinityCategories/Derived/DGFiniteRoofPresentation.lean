module
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofCoefficientTransport

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {K : SSet.{max u v}}
variable (r : K ⟶ dgRoofCorrespondence A D P x y)

/-- 一つの実閉分母上の全係数と、元の実屋根図式への全輸送。 -/
structure DGFiniteRoofPresentation where
  denominator : DGClosedVerdierDenominators A D P x
  coefficient : K ⟶ DGNerve.pinchedHom A D
    (ForgetEnrichment.to (Complex A) denominator.obj.left) y
  transport : SSet.Homotopy
    (coefficient ≫ dgClosedRoofHomInclusion A D P x y denominator) r

/-- 任意の有限実屋根図式は、一つの実閉分母上に全ホモトピー付きで表示できる。 -/
theorem dgFiniteRoofPresentation_nonempty [IsDGPretriangulated A D] [K.Finite] :
    Nonempty (DGFiniteRoofPresentation A D P x y r) := by
  obtain ⟨c⟩ := dgVerdierFiniteJoinCone_nonempty A D
    (r ≫ dgRoofCorrespondenceProjection A D P x y)
  obtain ⟨R⟩ := roofRelativeFiberReduction_of_cone
    (i := 𝟙 K) (p := dgRoofCorrespondenceProjection A D P x y)
    (q := dgRoofCorrespondenceProjection A D P x y) (F := 𝟙 _) (a := r) (g := r)
    (Category.id_comp _) (by simp only [Category.id_comp, Category.comp_id]) c
  let d := dgVerdierOverVertexClosed A D P x R.cone.vertex
  let f := R.boundary ≫ (dgRoofCorrespondenceFiberIso A D P x y R.cone.vertex).hom
  have hd : dgClosedRoofHomInclusion A D P x y d =
      dgRoofHomInclusion A D P x y R.cone.vertex :=
    dgRoofHomInclusion_vertex_transport A D P x y
      (dgVerdierOverVertexClosed_vertex A D P x R.cone.vertex)
  have hf : f ≫ dgClosedRoofHomInclusion A D P x y d =
      R.boundary ≫ vertexFiberι (dgRoofCorrespondenceProjection A D P x y) R.cone.vertex := by
    rw [hd]
    change (R.boundary ≫ (dgRoofCorrespondenceFiberIso A D P x y R.cone.vertex).hom) ≫
      ((dgRoofCorrespondenceFiberIso A D P x y R.cone.vertex).inv ≫ _) = _
    rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact ⟨⟨d, f, stableHomotopyRetarget R.boundaryTransport hf.symm rfl⟩⟩

end SerrePositivity.InfinityCategories
