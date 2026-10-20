module
public import SerrePositivity.InfinityCategories.Derived.RoofEndpointTransport
public import SerrePositivity.InfinityCategories.Derived.DGInvertingRoofFunctor
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap
/-!
概要：商関手自身の任意標的屋根を、実商屋根と両射影・固定 Hom 包含ごと同定する。
方針：商像の標準頂点への等式輸送を明示し、全次元の slice 射影を照合する。
規約：端点の等式輸送を省略しない。使われ方：商内の実評価族と実 AW 合成の照合。
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
/-- 商関手自身の任意標的屋根と、実商屋根の標準同型。 -/
def dgQuotientInvertingRoofIso (P : Set D) (x y : D) :
    dgInvertingRoof A D P x (dgQuotientNerveProjection A D P)
      ((dgQuotientNerveProjection A D P).app (Opposite.op ⦋0⦌) (Simplex.vertex y)) ≅
        dgQuotientRoofCorrespondence A D P x y :=
  roofEndpointIso (dgVerdierOverSource A D P x ≫ dgQuotientNerveProjection A D P)
    (dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y)
/-- 標準同型は、元の実屋根からの商比較と全次元で可換。 -/
lemma dgQuotientInvertingRoofIso_comparison (P : Set D) (x y : D) :
    dgInvertingRoofFunctorMap A D P x y (dgQuotientNerveProjection A D P) ≫
      (dgQuotientInvertingRoofIso A D P x y).hom = dgRoofCorrespondenceMap A D P x y := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    change _ ≫ ((roofEndpointIso _ _).hom ≫ pullback.fst _ _) = _
    rw [roofEndpointIso_fst, ← Category.assoc, dgInvertingRoofFunctorMap_target,
      dgRoofCorrespondenceMap_target, Category.assoc]
    exact congrArg (fun a => pullback.fst _ _ ≫ a)
      (roofTargetSliceMap_endpointTransport (dgQuotientNerveProjection A D P)
        (Simplex.vertex y) (dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y)
        (dgQuotientNervePoint A D P y))
  · rw [Category.assoc]
    change _ ≫ ((roofEndpointIso _ _).hom ≫ pullback.snd _ _) = _
    rw [roofEndpointIso_snd]
    exact (dgInvertingRoofFunctorMap_projection A D P x y (dgQuotientNerveProjection A D P)).trans
      (dgRoofCorrespondenceMap_projection A D P x y).symm

variable [IsDGPretriangulated A D]
/-- 実商 Hom の恒等分母包含の標的 slice 成分。 -/
lemma dgQuotientFixedHomRoofMap_target (P : Set D) (x y : D) :
    dgQuotientFixedHomRoofMap A D P x y ≫ pullback.fst _ _ =
      pinchedFamilySlice (dgQuotientNerve A D P)
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj y)) := by
  dsimp only [dgQuotientFixedHomRoofMap]
  rw [Category.assoc, ← dgQuotientRoofCorrespondenceFiberIso_hom_target,
    Iso.inv_hom_id_assoc]
  rfl
/-- 実商 Hom の恒等分母包含の実添字成分。 -/
lemma dgQuotientFixedHomRoofMap_projection (P : Set D) (x y : D) :
    dgQuotientFixedHomRoofMap A D P x y ≫ dgQuotientRoofCorrespondenceProjection A D P x y =
      SSet.const (dgVerdierOverIdentityVertex A D P x) := by
  dsimp only [dgQuotientFixedHomRoofMap]
  rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]
/-- 標準同型は、固定 Hom の包含と端点の等式輸送ごと可換。 -/
lemma dgQuotientInvertingRoofIso_fixedHom (P : Set D) (x y : D) :
    dgInvertingFixedHomRoofMap A D P x (dgQuotientNerveProjection A D P)
      ((dgQuotientNerveProjection A D P).app (Opposite.op ⦋0⦌) (Simplex.vertex y)) ≫
        (dgQuotientInvertingRoofIso A D P x y).hom =
    (pinchedEndpointIso (dgFunctorNerve_vertex (DGQuotient.inclusion A D P) x)
      (dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y)).hom ≫
        dgQuotientFixedHomRoofMap A D P x y := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    change _ ≫ ((roofEndpointIso _ _).hom ≫ pullback.fst _ _) = _
    rw [roofEndpointIso_fst, ← Category.assoc, dgInvertingFixedHomRoofMap_target]
    exact (pinchedFamilySlice_endpointTransport
      (dgFunctorNerve_vertex (DGQuotient.inclusion A D P) x)
      (dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y)).trans
        ((congrArg (fun a => (pinchedEndpointIso
          (dgFunctorNerve_vertex (DGQuotient.inclusion A D P) x)
          (dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y)).hom ≫ a)
          (dgQuotientFixedHomRoofMap_target A D P x y).symm).trans (Category.assoc _ _ _).symm)
  · rw [Category.assoc]
    change _ ≫ ((roofEndpointIso _ _).hom ≫ pullback.snd _ _) = _
    rw [roofEndpointIso_snd]
    change _ ≫ dgInvertingRoofProjection A D P x (dgQuotientNerveProjection A D P) _ = _
    rw [dgInvertingFixedHomRoofMap_projection]
    exact (SSet.comp_const _ _).symm.trans
      ((congrArg (fun a => (pinchedEndpointIso
        (dgFunctorNerve_vertex (DGQuotient.inclusion A D P) x)
        (dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y)).hom ≫ a)
        (dgQuotientFixedHomRoofMap_projection A D P x y).symm).trans (Category.assoc _ _ _).symm)
end SerrePositivity.InfinityCategories
