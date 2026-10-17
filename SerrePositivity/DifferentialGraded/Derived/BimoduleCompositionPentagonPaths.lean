module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorComparison

/-! # 全導来bimodule合成の五角図式の両経路 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t x
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]
variable (hE : localHomKFlat A E) (hF : localHomKFlat A F) (hG : localHomKFlat A G)
  (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E F)
  (S : DerivedBimoduleCategory A F G)

def derivedBimodulePentagonShort :
    (derivedBimoduleComposeFunctor A B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R ⋙
        (derivedBimoduleComposeFunctor A B F G hG).obj S ⟶
      (derivedBimoduleComposeFunctor A B C G hG).obj
        (((derivedBimoduleComposeFunctor A C E G hG).obj
          (((derivedBimoduleComposeFunctor A E F G hG).obj S).obj R)).obj Q) :=
  whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj Q)
      (derivedBimoduleAssociator A B E F G hF hG R S).hom ≫
    (derivedBimoduleAssociator A B C E G hE hG Q
      (((derivedBimoduleComposeFunctor A E F G hG).obj S).obj R)).hom

def derivedBimodulePentagonLong :
    (derivedBimoduleComposeFunctor A B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R ⋙
        (derivedBimoduleComposeFunctor A B F G hG).obj S ⟶
      (derivedBimoduleComposeFunctor A B C G hG).obj
        (((derivedBimoduleComposeFunctor A C E G hG).obj
          (((derivedBimoduleComposeFunctor A E F G hG).obj S).obj R)).obj Q) :=
  whiskerRight (derivedBimoduleAssociator A B C E F hE hF Q R).hom
      ((derivedBimoduleComposeFunctor A B F G hG).obj S) ≫
    (derivedBimoduleAssociator A B C F G hF hG
      (((derivedBimoduleComposeFunctor A C E F hF).obj R).obj Q) S).hom ≫
    (derivedBimoduleComposeFunctor A B C G hG).map
      ((derivedBimoduleAssociator A C E F G hF hG R S).hom.app Q)

end SerrePositivity.DifferentialGraded.BimoduleTensor
