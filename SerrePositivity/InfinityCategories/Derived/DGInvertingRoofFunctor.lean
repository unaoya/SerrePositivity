module
public import SerrePositivity.InfinityCategories.Derived.DGInvertingRoof
public import SerrePositivity.InfinityCategories.Derived.RoofFunctorCorrespondence
public import SerrePositivity.InfinityCategories.Derived.DGQuotientFixedHomRoof

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 任意の関手による、元の実屋根全体の標的への変換。 -/
def dgInvertingRoofFunctorMap (P : Set D) (x y : D) {Y : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) :
    dgRoofCorrespondence A D P x y ⟶
      dgInvertingRoof A D P x F (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) :=
  roofFunctorMap (dgVerdierOverSource A D P x) _ F rfl (Simplex.vertex y)

omit [Small.{u} D] in
/-- 元の実屋根の標的変換は、実分母を厳密に固定する。 -/
lemma dgInvertingRoofFunctorMap_projection (P : Set D) (x y : D)
    {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y) :
    dgInvertingRoofFunctorMap A D P x y F ≫ dgInvertingRoofProjection A D P x F
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) =
    dgRoofCorrespondenceProjection A D P x y :=
  roofFunctorMap_snd _ _ _ _ _

omit [Small.{u} D] in
/-- 元の実屋根の標的変換の実射側は、標的 slice の後合成。 -/
lemma dgInvertingRoofFunctorMap_target (P : Set D) (x y : D)
    {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y) :
    dgInvertingRoofFunctorMap A D P x y F ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ roofTargetSliceMap F (Simplex.vertex y) :=
  roofFunctorMap_fst _ _ _ _ _

variable [IsDGPretriangulated A D]

/-- 元の恒等分母の固定 Hom の包含の実射側成分。 -/
lemma dgOriginalFixedHomRoofMap_target (P : Set D) (x y : D) :
    dgOriginalFixedHomRoofMap A D P x y ≫ pullback.fst _ _ =
      (pinchedHomSliceFiberIso (X := dgNerve A D) (Simplex.vertex x)
        (Simplex.vertex y)).hom ≫
      vertexFiberι (sliceOverProjection
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)))
        (Simplex.vertex x) := by
  dsimp only [dgOriginalFixedHomRoofMap]
  rw [Category.assoc, ← dgRoofCorrespondenceFiberIso_hom_target,
    Iso.inv_hom_id_assoc]
  rfl

/-- 元の固定 Hom の包含も実恒等分母上にある。 -/
lemma dgOriginalFixedHomRoofMap_projection (P : Set D) (x y : D) :
    dgOriginalFixedHomRoofMap A D P x y ≫ dgRoofCorrespondenceProjection A D P x y =
      SSet.const (dgVerdierOverIdentityVertex A D P x) := by
  dsimp only [dgOriginalFixedHomRoofMap]
  rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]

/-- 任意標的への実屋根変換は、元の固定 Hom に対する関手の作用と厳密に可換。 -/
theorem dgInvertingRoofFunctorMap_fixedHom (P : Set D) (x y : D)
    {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y) :
    dgOriginalFixedHomRoofMap A D P x y ≫ dgInvertingRoofFunctorMap A D P x y F =
      pinchedHomMap F (Simplex.vertex x) (Simplex.vertex y) ≫
        dgInvertingFixedHomRoofMap A D P x F (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, dgInvertingRoofFunctorMap_target, ← Category.assoc,
      dgOriginalFixedHomRoofMap_target, Category.assoc, roofTargetSliceMap_pinched,
      Category.assoc, dgInvertingFixedHomRoofMap_target]
  · change _ ≫ dgInvertingRoofProjection A D P x F _ = _ ≫
      dgInvertingRoofProjection A D P x F _
    rw [Category.assoc, dgInvertingRoofFunctorMap_projection,
      dgOriginalFixedHomRoofMap_projection, Category.assoc,
      dgInvertingFixedHomRoofMap_projection, SSet.comp_const]

end SerrePositivity.InfinityCategories
