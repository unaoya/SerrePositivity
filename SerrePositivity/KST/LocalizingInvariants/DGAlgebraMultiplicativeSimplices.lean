module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionContravariant
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainComonoid
public import Mathlib.CategoryTheory.Whiskering

/-!
概要：実 AW 余単体から dg 代数の乗法的単体的対象を構成する。
方針：E2 の共変な余モノイド関手と Sp の反変畳み込みを合成する。
規約：導来写像空間との比較・Kan 性はここでは主張しない。
使われ方：Postnikov 錐の全導来写像空間による検証の単体模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

/-- 概要：底の代数射の全余モノイドにわたる自然性。
方針：内部 Hom 前合成の全自然性を使う。規約：対象別比較で代用しない。
使われ方：標的代数に対する単体模型の関手性。 -/
def convolutionTargetNatTrans {B C : Mon (Complex R)} (g : B ⟶ C) :
    convolutionContravariant R B ⟶ convolutionContravariant R C where
  app H := (convolutionFunctor R H.unop).map g
  naturality _ _ f := by
    apply Mon.Hom.ext'
    exact ((MonoidalClosed.pre f.unop.hom).naturality g.hom).symm

def multiplicativeSimplices (B : Mon (Complex R)) :
    SimplexCategoryᵒᵖ ⥤ Mon (Complex R) :=
  (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexCochainComonFunctor R).op ⋙
    convolutionContravariant R B

def multiplicativeSimplicesMap {B C : Mon (Complex R)} (g : B ⟶ C) :
    multiplicativeSimplices R B ⟶ multiplicativeSimplices R C :=
  Functor.whiskerLeft (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexCochainComonFunctor R).op
    (convolutionTargetNatTrans R g)

lemma multiplicativeSimplices_obj_X (B : Mon (Complex R)) (n : SimplexCategoryᵒᵖ) :
    ((multiplicativeSimplices R B).obj n).X =
      homComplex R (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains R (SSet.stdSimplex.obj n.unop)) B.X := rfl

def multiplicativeMappingSimplices (A B : Mon (Complex R)) : SSet.{u} :=
  multiplicativeSimplices R B ⋙ coyoneda.obj (Opposite.op A)

def multiplicativeMappingPrecompose {A A' : Mon (Complex R)} (f : A' ⟶ A)
    (B : Mon (Complex R)) :
    multiplicativeMappingSimplices R A B ⟶ multiplicativeMappingSimplices R A' B :=
  Functor.whiskerLeft (multiplicativeSimplices R B) (coyoneda.map f.op)

def multiplicativeMappingPostcompose (A : Mon (Complex R)) {B C : Mon (Complex R)}
    (g : B ⟶ C) :
    multiplicativeMappingSimplices R A B ⟶ multiplicativeMappingSimplices R A C :=
  Functor.whiskerRight (multiplicativeSimplicesMap R g) (coyoneda.obj (Opposite.op A))

def multiplicativeSimplicesFunctor :
    Mon (Complex R) ⥤ (SimplexCategoryᵒᵖ ⥤ Mon (Complex R)) where
  obj := multiplicativeSimplices R
  map := multiplicativeSimplicesMap R
  map_id B := by
    apply NatTrans.ext
    funext n
    apply Mon.Hom.ext'
    exact (ihom _).map_id B.X
  map_comp f g := by
    apply NatTrans.ext
    funext n
    apply Mon.Hom.ext'
    exact (ihom _).map_comp f.hom g.hom

def multiplicativeMappingFunctor (A : Mon (Complex R)) : Mon (Complex R) ⥤ SSet.{u} :=
  multiplicativeSimplicesFunctor R ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ (Mon (Complex R)) (Type u)).obj
      (coyoneda.obj (Opposite.op A))

lemma multiplicativeMappingFunctor_obj (A B : Mon (Complex R)) :
    (multiplicativeMappingFunctor R A).obj B = multiplicativeMappingSimplices R A B := rfl

lemma multiplicativeMappingFunctor_map (A : Mon (Complex R)) {B C : Mon (Complex R)}
    (g : B ⟶ C) :
    (multiplicativeMappingFunctor R A).map g = multiplicativeMappingPostcompose R A g := rfl

lemma multiplicativeMapping_pre_post {A A' B C : Mon (Complex R)} (f : A' ⟶ A) (g : B ⟶ C) :
    multiplicativeMappingPrecompose R f B ≫ multiplicativeMappingPostcompose R A' g =
      multiplicativeMappingPostcompose R A g ≫ multiplicativeMappingPrecompose R f C := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro a
  exact Category.assoc f a _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
