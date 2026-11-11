module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.FunctorHomCategory

/-!
概要：任意単体集合から通常圏の nerve への関手圏を、h 圏上の通常関手圏と比較する。
方針：h の積比較同型を、指数随伴と nerve 随伴の合成の間で共役する。
規約：始域を通常圏の nerve に制限しない。使われ方：局所化の普遍性の h 圏への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor MonoidalClosed MonoidalCategory SSet
namespace SerrePositivity.KST.LocalizingInvariants

def homotopyNerveExponentialNatIso (X : SSet.{u}) :
    ihom (hoFunctor.obj X) ⋙ nerveFunctor ≅ nerveFunctor ⋙ ihom X :=
  conjugateIsoEquiv (nerveAdjunction.comp (ihom.adjunction (hoFunctor.obj X)))
    ((ihom.adjunction X).comp nerveAdjunction)
    (asIso (CartesianMonoidalCategory.prodComparisonNatTrans hoFunctor X))

def homotopyNerveExponentialIso (X : SSet.{u}) (A : Type u) [Category.{u} A] :
    nerve (hoFunctor.obj X ⥤ A) ≅ (ihom X).obj (nerve A) :=
  (homotopyNerveExponentialNatIso X).app (Cat.of A)

lemma homotopyNerveExponentialNatIso_precomp {X Y : SSet.{u}} (f : X ⟶ Y) :
    (homotopyNerveExponentialNatIso Y).hom ≫
        whiskerLeft nerveFunctor (pre f) =
      whiskerRight (pre (hoFunctor.map f)) nerveFunctor ≫
        (homotopyNerveExponentialNatIso X).hom := by
  let a := nerveAdjunction.comp (ihom.adjunction (hoFunctor.obj Y))
  let b := (ihom.adjunction Y).comp nerveAdjunction
  let c := (ihom.adjunction X).comp nerveAdjunction
  let d := nerveAdjunction.comp (ihom.adjunction (hoFunctor.obj X))
  have h : whiskerRight ((curriedTensor SSet).map f) hoFunctor ≫
        CartesianMonoidalCategory.prodComparisonNatTrans hoFunctor Y =
      CartesianMonoidalCategory.prodComparisonNatTrans hoFunctor X ≫
        whiskerLeft hoFunctor ((curriedTensor Cat).map (hoFunctor.map f)) := by
    apply NatTrans.ext
    funext Z
    exact CartesianMonoidalCategory.prodComparison_natural_whiskerRight hoFunctor (B := Z) f
  have k := congrArg (conjugateEquiv a c) h
  rw [← conjugateEquiv_comp a b c, ← conjugateEquiv_comp a d c] at k
  simpa only [a, b, c, d, conjugateEquiv_whiskerRight,
    conjugateEquiv_whiskerLeft, MonoidalClosed.pre,
    homotopyNerveExponentialNatIso, conjugateIsoEquiv_apply_hom, asIso_hom] using k

lemma homotopyNerveExponentialIso_precomp {X Y : SSet.{u}} (f : X ⟶ Y)
    (A : Type u) [Category.{u} A] :
    nerveMap ((whiskeringLeft (hoFunctor.obj X) (hoFunctor.obj Y) A).obj
        (hoFunctor.map f).toFunctor) ≫ (homotopyNerveExponentialIso X A).hom =
      (homotopyNerveExponentialIso Y A).hom ≫ (pre f).app (nerve A) := by
  have h := NatTrans.congr_app (homotopyNerveExponentialNatIso_precomp f) (Cat.of A)
  have hp : (pre (hoFunctor.map f)).app (Cat.of A) =
      ((whiskeringLeft (hoFunctor.obj X) (hoFunctor.obj Y) A).obj
        (hoFunctor.map f).toFunctor).toCatHom := by
    apply uncurry_injective
    rw [MonoidalClosed.uncurry_pre]
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun x => rfl) (fun x y g => ?_)
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  change (homotopyNerveExponentialIso Y A).hom ≫ (pre f).app (nerve A) =
    nerveFunctor.map ((pre (hoFunctor.map f)).app (Cat.of A)) ≫
      (homotopyNerveExponentialIso X A).hom at h
  rw [hp] at h
  exact h.symm

lemma homotopyNerveExponentialIso_postcomp (X : SSet.{u}) {A B : Type u}
    [Category.{u} A] [Category.{u} B] (F : A ⥤ B) :
    nerveMap ((whiskeringRight (hoFunctor.obj X) A B).obj F) ≫
        (homotopyNerveExponentialIso X B).hom =
      (homotopyNerveExponentialIso X A).hom ≫ (ihom X).map (nerveMap F) :=
  (homotopyNerveExponentialNatIso X).hom.naturality F.toCatHom

def homotopyNerveFunctorCategoryEquivalence (X : SSet.{u}) (A : Type u) [Category.{u} A] :
    hoFunctor.obj ((ihom X).obj (nerve A)) ≌ (hoFunctor.obj X ⥤ A) :=
  Cat.equivOfIso (hoFunctor.mapIso (homotopyNerveExponentialIso X A).symm ≪≫
    nerveFunctorCompHoFunctorIso.app (Cat.of (hoFunctor.obj X ⥤ A)))

end SerrePositivity.KST.LocalizingInvariants
