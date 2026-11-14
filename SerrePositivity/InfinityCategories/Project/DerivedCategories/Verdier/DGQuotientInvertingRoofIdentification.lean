module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofEndpointTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGInvertingRoofFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGFunctorPinchedMap
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
/-- 商関手自身の任意標的屋根と、実商屋根の標準同型。 -/
def dgQuotientInvertingRoofIso (P : Set D) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoof A D P x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) ≅
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondence A D P x y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEndpointIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y)
/-- 標準同型は、元の実屋根からの商比較と全次元で可換。 -/
lemma dgQuotientInvertingRoofIso_comparison (P : Set D) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) ≫
      (dgQuotientInvertingRoofIso A D P x y).hom = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    change _ ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEndpointIso _ _).hom ≫ pullback.fst _ _) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEndpointIso_fst, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap_target,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap_target, Category.assoc]
    exact congrArg (fun a => pullback.fst _ _ ≫ a)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofTargetSliceMap_endpointTransport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNervePoint A D P y))
  · rw [Category.assoc]
    change _ ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEndpointIso _ _).hom ≫ pullback.snd _ _) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEndpointIso_snd]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap_projection A D P x y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap_projection A D P x y).symm

variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 実商 Hom の恒等分母包含の標的 slice 成分。 -/
lemma dgQuotientFixedHomRoofMap_target (P : Set D) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj y)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap]
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceFiberIso_hom_target,
    Iso.inv_hom_id_assoc]
  rfl
/-- 実商 Hom の恒等分母包含の実添字成分。 -/
lemma dgQuotientFixedHomRoofMap_projection (P : Set D) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
/-- 標準同型は、固定 Hom の包含と端点の等式輸送ごと可換。 -/
lemma dgQuotientInvertingRoofIso_fixedHom (P : Set D) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) ≫
        (dgQuotientInvertingRoofIso A D P x y).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (DGQuotient.inclusion A D P) x)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    change _ ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEndpointIso _ _).hom ≫ pullback.fst _ _) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEndpointIso_fst, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_target]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedFamilySlice_endpointTransport
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (DGQuotient.inclusion A D P) x)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y)).trans
        ((congrArg (fun a => (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (DGQuotient.inclusion A D P) x)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y)).hom ≫ a)
          (dgQuotientFixedHomRoofMap_target A D P x y).symm).trans (Category.assoc _ _ _).symm)
  · rw [Category.assoc]
    change _ ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEndpointIso _ _).hom ≫ pullback.snd _ _) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEndpointIso_snd]
    change _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofProjection A D P x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_projection]
    exact (SSet.comp_const _ _).symm.trans
      ((congrArg (fun a => (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (DGQuotient.inclusion A D P) x)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y)).hom ≫ a)
        (dgQuotientFixedHomRoofMap_projection A D P x y).symm).trans (Category.assoc _ _ _).symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
