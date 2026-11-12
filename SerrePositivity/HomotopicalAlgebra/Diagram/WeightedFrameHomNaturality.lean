module

public import SerrePositivity.HomotopicalAlgebra.Diagram.SmallHomWeightAdjunctionNaturality
public import SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexCosimplicialHom

/-! # Two-variable natural weighted-frame Hom isomorphism

The actual adjunction Hom isomorphism and simplicial Yoneda commute with
source-frame maps. This is an isomorphism of actual bifunctors after the
explicit common-universe lifts, with no simplicial enrichment on C.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.SmallHomFrameWeights
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [HomotopicalAlgebra.ModelCategory C] [IsLocallyPresentable.{w} C]
  (W : Kᵒᵖ ⥤ SSet.{w})

abbrev standardFrameFamily : (K ⥤ SimplexCategory ⥤ C) ⥤ SimplexCategory ⥤ C :=
  weightedFamily K W ⋙ (Functor.whiskeringLeft SimplexCategory SSet.{w} C).obj SSet.stdSimplex

abbrev standardFrameHomFamily : (K ⥤ SimplexCategory ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{v} :=
  (standardFrameFamily K W).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

def standardFrameHomIso (A : K ⥤ SimplexCategory ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((standardFrameFamily K W).obj A) ⋙ SSet.uliftFunctor.{w,v} ≅
      weightedHom K A W ⋙ SSet.uliftFunctor.{v,w} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIso (weightedAdjunction K A W) SSet.stdSimplex ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight QuillenStandardFrame.homIso SSet.uliftFunctor ≪≫
        Functor.leftUnitor _)

/-- Source-frame and target naturality hold simultaneously. -/
def standardFrameHomFamilyIso :
    standardFrameHomFamily K W ⋙
        (Functor.whiskeringRight C SSet.{v} SSet.{max v w}).obj SSet.uliftFunctor.{w,v} ≅
      weightedHomFamily K W ⋙
        (Functor.whiskeringRight C SSet.{w} SSet.{max v w}).obj SSet.uliftFunctor.{v,w} :=
  NatIso.ofComponents (fun A => standardFrameHomIso K W A.unop) (by
    intro A B a
    apply NatTrans.ext
    funext Y
    apply NatTrans.ext
    funext n
    ext h
    apply ULift.ext
    exact (congrArg SSet.yonedaEquiv
      (weightedHomEquiv_frame_naturality K a.unop W (SSet.stdSimplex.obj n.unop) Y h.down)).trans
        (SSet.yonedaEquiv_comp _ _))

end SerrePositivity.DiagramModel.SmallHomFrameWeights
