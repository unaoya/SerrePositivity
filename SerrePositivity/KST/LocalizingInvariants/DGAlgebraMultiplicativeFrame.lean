module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMultiplicativeMatching
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMultiplicativeReedyUnderlying

/-!
概要：実 AW 乗法的単体模型への定数増大と frame 条件。
方針：元の余単位の代数射を全単体・全標的に自然な増大へ束ねる。
規約：実 matching の全射性・全単体作用素の擬同型性・零単体の同型性を用いる。
使われ方：実 dg 代数の導来写像空間比較に進むための具体的 frame。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

def convolutionConstantNatTrans (B : Mon (Complex R)) :
    (Functor.const (Comon (Complex R))ᵒᵖ).obj B ⟶ convolutionContravariant R B where
  app H := convolutionConstantMap R H.unop B
  naturality H K f := by
    change 𝟙 B ≫ convolutionConstantMap R K.unop B =
      convolutionConstantMap R H.unop B ≫ convolutionPrecompose R f.unop B
    rw [Category.id_comp, convolutionConstantMap_precompose]

def multiplicativeSimplicesAugmentation (B : Mon (Complex R)) :
    (Functor.const SimplexCategoryᵒᵖ).obj B ⟶ multiplicativeSimplices R B :=
  Functor.whiskerLeft (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexCochainComonFunctor R).op
    (convolutionConstantNatTrans R B)

def convolutionTargetFunctor :
    Mon (Complex R) ⥤ (Comon (Complex R))ᵒᵖ ⥤ Mon (Complex R) where
  obj := convolutionContravariant R
  map := convolutionTargetNatTrans R
  map_id B := by
    apply NatTrans.ext
    funext H
    apply Mon.Hom.ext'
    exact (ihom H.unop.X).map_id B.X
  map_comp f g := by
    apply NatTrans.ext
    funext H
    apply Mon.Hom.ext'
    exact (ihom H.unop.X).map_comp f.hom g.hom

def convolutionConstantFamily :
    Functor.const (Comon (Complex R))ᵒᵖ ⟶ convolutionTargetFunctor R where
  app := convolutionConstantNatTrans R
  naturality B C g := by
    apply NatTrans.ext
    funext H
    apply Mon.Hom.ext'
    exact congrArg Mon.Hom.hom (convolutionConstantMap_naturality R H.unop g).symm

def multiplicativeSimplicesConstant :
    Functor.const SimplexCategoryᵒᵖ ⟶ multiplicativeSimplicesFunctor R :=
  Functor.whiskerRight (convolutionConstantFamily R)
    ((Functor.whiskeringLeft SimplexCategoryᵒᵖ (Comon (Complex R))ᵒᵖ
      (Mon (Complex R))).obj
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexCochainComonFunctor R).op)

lemma multiplicativeSimplicesAugmentation_quasiIso (B : Mon (Complex R))
    (n : SimplexCategoryᵒᵖ) :
    QuasiIso ((multiplicativeSimplicesAugmentation R B).app n).hom :=
  simplexConstant_quasiIso R n.unop B

lemma multiplicativeSimplicesAugmentation_zero_isIso (B : Mon (Complex R)) :
    IsIso ((multiplicativeSimplicesAugmentation R B).app (Opposite.op ⦋0⦌)) :=
  simplexConstant_zero_isIso R B

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
