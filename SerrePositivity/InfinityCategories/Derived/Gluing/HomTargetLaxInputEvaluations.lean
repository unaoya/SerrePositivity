module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxInputCoordinates
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedInputCoordinateUncurry
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedPullbackInputEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorRawIntervalEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCompositionTriangles
/-!
概要：元 lax Hom の入力座標の逆を元左右 Hom 複体の全 join 評価として回収する。
方針：同じ実比較の全射影・端点輸送・全入力を保持する。
規約：新たな主経路仮定を置かない。使われ方：K-S• の全 lax 比較。
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
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetLaxHomRawInputIso_inv_first_uncurry :
    pinchedHomUncurry (dgGluingHomTargetLaxHomRawInputIso R C D E p q X Y).inv ≫
      fst (dgNerve R C) (dgNerve R D) =
    pinchedHomUncurry (fst _ _ ≫
      (pinchedComplexModelIso (A := R) X.left Y.left).inv) := by
  dsimp only [dgGluingHomTargetLaxHomRawInputIso, Iso.trans_inv,
    dgGluingHomTargetLaxHomInputEndpointIso, dgGluingPinchedCompositeIso]
  rw [dgGluingPinchedEndpointIso_inv_uncurry,
    dgGluingPinchedTensorIso_inv_first_uncurry]
  simp only [tensorIso_inv, tensorHom_fst,
    dgGluingHomTargetLaxHomLeftRawInputIso, Iso.trans_inv, Category.assoc]
  rw [← Category.assoc, dgGluingPinchedEndpointIso_inv_uncurry]

lemma dgGluingHomTargetLaxHomRawInputIso_inv_second_uncurry :
    pinchedHomUncurry (dgGluingHomTargetLaxHomRawInputIso R C D E p q X Y).inv ≫
      snd (dgNerve R C) (dgNerve R D) =
    pinchedHomUncurry (snd _ _ ≫
      (pinchedComplexModelIso (A := R) X.right Y.right).inv) := by
  dsimp only [dgGluingHomTargetLaxHomRawInputIso, Iso.trans_inv,
    dgGluingHomTargetLaxHomInputEndpointIso, dgGluingPinchedCompositeIso]
  rw [dgGluingPinchedEndpointIso_inv_uncurry,
    dgGluingPinchedTensorIso_inv_second_uncurry]
  simp only [tensorIso_inv, tensorHom_snd,
    dgGluingHomTargetLaxHomRightRawInputIso, Iso.trans_inv, Category.assoc]
  rw [← Category.assoc, dgGluingPinchedEndpointIso_inv_uncurry]

lemma dgGluingHomTargetLaxHomIntervalInputBase_raw_evaluation :
    intervalMappingUncurry ((dgGluingHomTargetLaxHomRawInputIso R C D E p q X Y).inv ≫
      dgGluingHomTargetLaxHomIntervalInputBase R C D E p q X Y) =
    rightMappingSpacePrism _ ≫
      pinchedHomUncurry (dgGluingHomTargetLaxHomRawInputIso R C D E p q X Y).inv ≫
        (dgNerve.map p ⊗ₘ dgNerve.map q) :=
  dgGluingPinchedHomPullbackBaseMap_evaluation (F2.arrowEndpointPair (dgNerve R E))
    (dgNerve.map p ⊗ₘ dgNerve.map q)
    ((dgGluingHomTargetNerveLaxComparison R C D E p q).app (Opposite.op ⦋0⦌) (Simplex.vertex X))
    ((dgGluingHomTargetNerveLaxComparison R C D E p q).app (Opposite.op ⦋0⦌) (Simplex.vertex Y))
    (dgGluingHomTargetLaxHomRawInputIso R C D E p q X Y).inv

lemma dgGluingHomTargetLeftIntervalInput_raw_evaluation :
    intervalMappingUncurry (dgGluingHomTargetLeftIntervalInput R C D E p q X Y) =
    rightMappingSpacePrism _ ≫
      pinchedHomUncurry (pinchedComplexModelIso (A := R) X.left Y.left).inv ≫
        dgNerve.map p := by
  simpa only [dgGluingHomTargetLeftIntervalInput, dgGluingHomTargetLeftCoefficientInput,
    Category.assoc] using dgGluingFunctorRawIntervalEvaluation p X.left Y.left

lemma dgGluingHomTargetRightIntervalInput_raw_evaluation :
    intervalMappingUncurry (dgGluingHomTargetRightIntervalInput R C D E p q X Y) =
    rightMappingSpacePrism _ ≫
      pinchedHomUncurry (pinchedComplexModelIso (A := R) X.right Y.right).inv ≫
        dgNerve.map q := by
  simpa only [dgGluingHomTargetRightIntervalInput, dgGluingHomTargetRightCoefficientInput,
    Category.assoc] using dgGluingFunctorRawIntervalEvaluation q X.right Y.right

end SerrePositivity.InfinityCategories
