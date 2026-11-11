module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeBlocks
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeCoefficient
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
/-! 代表加群の閉射と augmentation の評価を、元の Hom 後合成と双加群の左作用へ戻す。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

lemma dgGluingYoneda_evaluate (x y z : C)
    (f : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z) :
    (moduleEvaluation R C x).map ((dgYoneda R C).onClosed.map f) =
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) x) f := by
  have hn := dgHomMap_postcompose (dgYoneda R C) (ForgetEnrichment.of (Complex R) x) f
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_postcompose R C x ((dgYoneda R C).onClosed.map f)
  change eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) x) f ≫
    yonedaHom R C x z = yonedaHom R C x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (representable R x))
        ((dgYoneda R C).onClosed.map f) at hn
  change eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) (representable R x)) ((dgYoneda R C).onClosed.map f) ≫
      (dgYonedaIso R x (representable R z)).hom =
    (dgYonedaIso R x (representable R y)).hom ≫
      (moduleEvaluation R C x).map ((dgYoneda R C).onClosed.map f) at he
  symm
  calc
    _ = (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) x) f ≫
      yonedaHom R C x z) ≫ (dgYonedaIso R x (representable R z)).hom := by
      simp only [yonedaHom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = (yonedaHom R C x y ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (representable R x)) ((dgYoneda R C).onClosed.map f)) ≫
        (dgYonedaIso R x (representable R z)).hom := by rw [hn]
    _ = _ := by
      rw [Category.assoc, he, ← Category.assoc]
      simp only [yonedaHom, Iso.inv_hom_id, Category.id_comp]

/-- 閉射の Hom cone を、同じ Yoneda 像の cone 加群からの全 Hom と同定する。 -/
def dgGluingYonedaConeIso (x y z : C)
    (f : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z) :
    mappingCone (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) x) f) ≅
      moduleHom R C (representable R x)
        (ForgetEnrichment.to (Complex R) (moduleCone R C ((dgYoneda R C).onClosed.map f))) :=
  eqToIso (congrArg (fun a : homObject R C x y ⟶ homObject R C x z => mappingCone a)
    (dgGluingYoneda_evaluate R C x y z f).symm) ≪≫
      (dgYonedaIso R x
        (ForgetEnrichment.to (Complex R) (moduleCone R C ((dgYoneda R C).onClosed.map f)))).symm

variable (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)

lemma dgGluingLeftModuleArrow_yoneda : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f) =
    (dgYoneda R C).onClosed.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M).onClosed.map f) := by
  change ForgetEnrichment.homOf (Complex R)
    (ForgetEnrichment.homTo (Complex R) f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftModule R C D M).map Y Z) =
    ForgetEnrichment.homOf (Complex R)
      (ForgetEnrichment.homTo (Complex R) f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M Y Z ≫
        yonedaHom R C Y.left Z.left)
  congr 1
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftModule_map]

lemma dgGluingLeftArrow_evaluate : (moduleEvaluation R C X.left).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftArrow R C D M X Y Z f := by
  rw [dgGluingLeftModuleArrow_yoneda]
  exact dgGluingYoneda_evaluate R C X.left Y.left Z.left ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M).onClosed.map f)

lemma dgGluingAugmentation_evaluate : (moduleEvaluation R C X.left).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction_yoneda R C D M X Y
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_postcompose R C X.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y)
  rw [hn, ← Category.assoc] at he
  simpa only [yonedaHom, Iso.inv_hom_id, Category.id_comp] using he

lemma dgGluingRightArrow_evaluate : (moduleEvaluation R C X.left).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeAction R C D M X Y Z f := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
