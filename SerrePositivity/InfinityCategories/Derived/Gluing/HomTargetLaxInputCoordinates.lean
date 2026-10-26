module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxIntervalTransport
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedCompositeTransport
public import SerrePositivity.InfinityCategories.F2.CatInfinity.PinchedHomTensorIso
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap
/-!
概要：元 lax Hom 標的の入力を元左右 Hom 複体の積へ厳密に移す。
方針：元二射影の対を保持し、端点輸送・積同型・実 Hom 模型同型を合成する。
規約：元入力を忘れない。使われ方：元二脚の全 lax 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "F" => dgGluingHomTargetNerveLaxComparison R C D E p q
lemma dgGluingHomTargetNerveLaxComparison_inputs :
    (F) ≫ pullback.snd (F2.arrowEndpointPair (dgNerve R E))
      (dgNerve.map p ⊗ₘ dgNerve.map q) =
    lift (dgNerve.map (dgGluingLeft R C D M)) (dgNerve.map (dgGluingRight R C D M)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst]
    simpa only [Category.assoc, F2.laxPullbackFst] using
      dgGluingHomTargetNerveLaxComparison_fst R C D E p q
  · rw [lift_snd]
    simpa only [Category.assoc, F2.laxPullbackSnd] using
      dgGluingHomTargetNerveLaxComparison_snd R C D E p q

variable (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetLaxHomInputEndpointIso :=
  dgGluingPinchedCompositeIso (F)
    (pullback.snd (F2.arrowEndpointPair (dgNerve R E)) (dgNerve.map p ⊗ₘ dgNerve.map q))
    (lift (dgNerve.map (dgGluingLeft R C D M)) (dgNerve.map (dgGluingRight R C D M)))
    (dgGluingHomTargetNerveLaxComparison_inputs R C D E p q)
    (Simplex.vertex X) (Simplex.vertex Y)

lemma dgGluingHomTargetLaxHomPullbackComparison_inputs_transport :
    dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y ≫
      dgGluingHomTargetLaxHomInputProjection R C D E p q X Y ≫
        (dgGluingHomTargetLaxHomInputEndpointIso R C D E p q X Y).hom =
    (dgGluingHomMappingIso R C D M X Y).inv ≫
      pinchedHomMap
        (lift (dgNerve.map (dgGluingLeft R C D M)) (dgNerve.map (dgGluingRight R C D M)))
        (Simplex.vertex X) (Simplex.vertex Y) := by
  rw [dgGluingHomTargetLaxHomInputProjection, dgGluingHomTargetLaxHomPullbackComparison,
    Category.assoc, reassoc_of% F2.laxPullbackMappingIso_inputs]
  simpa only [dgGluingHomTargetLaxHomMappingComparison,
    dgGluingHomTargetLaxHomInputEndpointIso, Category.assoc] using
    congrArg (fun k => (dgGluingHomMappingIso R C D M X Y).inv ≫ k)
      (dgGluingPinchedComposite_naturality (F)
        (pullback.snd (F2.arrowEndpointPair (dgNerve R E)) (dgNerve.map p ⊗ₘ dgNerve.map q))
        (lift (dgNerve.map (dgGluingLeft R C D M)) (dgNerve.map (dgGluingRight R C D M)))
        (dgGluingHomTargetNerveLaxComparison_inputs R C D E p q)
        (Simplex.vertex X) (Simplex.vertex Y))

def dgGluingHomTargetLaxHomLeftRawInputIso :=
  pinchedEndpointIso (dgFunctorNerve_vertex (dgGluingLeft R C D M) X)
    (dgFunctorNerve_vertex (dgGluingLeft R C D M) Y) ≪≫
      pinchedComplexModelIso (A := R) X.left Y.left

def dgGluingHomTargetLaxHomRightRawInputIso :=
  pinchedEndpointIso (dgFunctorNerve_vertex (dgGluingRight R C D M) X)
    (dgFunctorNerve_vertex (dgGluingRight R C D M) Y) ≪≫
      pinchedComplexModelIso (A := R) X.right Y.right

def dgGluingHomTargetLaxHomRawInputIso :=
  dgGluingHomTargetLaxHomInputEndpointIso R C D E p q X Y ≪≫
    F2.pinchedHomTensorIso
      ((lift (dgNerve.map (dgGluingLeft R C D M))
        (dgNerve.map (dgGluingRight R C D M))).app (Opposite.op ⦋0⦌) (Simplex.vertex X))
      ((lift (dgNerve.map (dgGluingLeft R C D M))
        (dgNerve.map (dgGluingRight R C D M))).app (Opposite.op ⦋0⦌) (Simplex.vertex Y)) ≪≫
    tensorIso (dgGluingHomTargetLaxHomLeftRawInputIso R C D E p q X Y)
      (dgGluingHomTargetLaxHomRightRawInputIso R C D E p q X Y)

end SerrePositivity.InfinityCategories
