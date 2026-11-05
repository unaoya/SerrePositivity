module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetArrowComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxHomComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedCompositeTransport
/-!
概要：元 lax Hom 比較の矢印射影を、同じ元 augmentation 全族の実作用へ回収する。
方針：F2 の Hom 引き戻し表示と、合成関手の端点輸送の自然性を使う。
規約：比較の実射を変更しない。使われ方：指定 lax Hom 比較への逆・往復則の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "F" => dgGluingHomTargetNerveLaxComparison R C D E p q

def dgGluingHomTargetLaxArrowEndpointIso :=
  dgGluingPinchedCompositeIso (F)
    (F2.laxPullbackArrow (dgNerve.map p) (dgNerve.map q))
    (dgGluingHomTargetAugmentationArrowFamily R C D E p q)
    (dgGluingHomTargetNerveLaxComparison_arrow R C D E p q)
    (Simplex.vertex X) (Simplex.vertex Y)

def dgGluingHomTargetLaxHomArrowProjection :
    dgGluingHomTargetLaxHomPullback R C D E p q X Y ⟶
      InfinityCategories.pinchedHom
        ((F2.laxPullbackArrow (dgNerve.map p) (dgNerve.map q)).app (Opposite.op ⦋0⦌)
          ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex X)))
        ((F2.laxPullbackArrow (dgNerve.map p) (dgNerve.map q)).app (Opposite.op ⦋0⦌)
          ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex Y))) :=
  pullback.fst _ _

attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetLaxHomPullbackComparison_arrow :
    dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y ≫
      dgGluingHomTargetLaxHomArrowProjection R C D E p q X Y =
    dgGluingHomTargetLaxHomMappingComparison R C D E p q X Y ≫
      pinchedHomMap (F2.laxPullbackArrow (dgNerve.map p) (dgNerve.map q))
        ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex X))
        ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex Y)) := by
  rw [dgGluingHomTargetLaxHomArrowProjection,
    dgGluingHomTargetLaxHomPullbackComparison, Category.assoc,
    F2.laxPullbackMappingIso_arrow]

lemma dgGluingHomTargetLaxHomPullbackComparison_arrow_transport :
    dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y ≫
      dgGluingHomTargetLaxHomArrowProjection R C D E p q X Y ≫
        (dgGluingHomTargetLaxArrowEndpointIso R C D E p q X Y).hom =
    (dgGluingHomMappingIso R C D M X Y).inv ≫
      pinchedHomMap (dgGluingHomTargetAugmentationArrowFamily R C D E p q)
        (Simplex.vertex X) (Simplex.vertex Y) := by
  rw [← Category.assoc, dgGluingHomTargetLaxHomPullbackComparison_arrow,
    dgGluingHomTargetLaxHomMappingComparison]
  simpa only [Category.assoc, dgGluingHomTargetLaxArrowEndpointIso] using
    congrArg (fun k => (dgGluingHomMappingIso R C D M X Y).inv ≫ k)
      (dgGluingPinchedComposite_naturality (F)
        (F2.laxPullbackArrow (dgNerve.map p) (dgNerve.map q))
        (dgGluingHomTargetAugmentationArrowFamily R C D E p q)
        (dgGluingHomTargetNerveLaxComparison_arrow R C D E p q)
        (Simplex.vertex X) (Simplex.vertex Y))

end SerrePositivity.InfinityCategories
