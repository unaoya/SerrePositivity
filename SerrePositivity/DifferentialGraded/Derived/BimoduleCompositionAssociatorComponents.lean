module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorKFlat

/-! # 全導来結合同型の成分と二つの後因子に関する同時自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

/-- 任意の二つの導来後因子で評価した、前因子全体に自然な結合同型。 -/
def derivedBimoduleAssociator (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E F) :
    (derivedBimoduleComposeFunctor A B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R ≅
      (derivedBimoduleComposeFunctor A B C F hF).obj
        (((derivedBimoduleComposeFunctor A C E F hF).obj R).obj Q) :=
  ((derivedBimoduleAssociatorIso A B C E F hE hF).app R).app Q

lemma derivedBimoduleAssociator_naturality (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) {Q Q' : DerivedBimoduleCategory A C E}
    {R R' : DerivedBimoduleCategory A E F} (f : Q ⟶ Q') (g : R ⟶ R') :
    derivedBimoduleComposePairMap A B C E F hE hF f g ≫
        (derivedBimoduleAssociator A B C E F hE hF Q' R').hom =
      (derivedBimoduleAssociator A B C E F hE hF Q R).hom ≫
        (derivedBimoduleComposeFunctor A B C F hF).map
          (derivedBimoduleComposeInnerMap A C E F hF f g) := by
  have hQ := ((derivedBimoduleAssociatorIso A B C E F hE hF).hom.app R).naturality f
  have hR := NatTrans.congr_app
    ((derivedBimoduleAssociatorIso A B C E F hE hF).hom.naturality g) Q'
  change whiskerRight ((derivedBimoduleComposeFunctor A B C E hE).map f)
      ((derivedBimoduleComposeFunctor A B E F hF).obj R) ≫
      (derivedBimoduleAssociator A B C E F hE hF Q' R).hom =
    (derivedBimoduleAssociator A B C E F hE hF Q R).hom ≫
      (derivedBimoduleComposeFunctor A B C F hF).map
        (((derivedBimoduleComposeFunctor A C E F hF).obj R).map f) at hQ
  change whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj Q')
      ((derivedBimoduleComposeFunctor A B E F hF).map g) ≫
      (derivedBimoduleAssociator A B C E F hE hF Q' R').hom =
    (derivedBimoduleAssociator A B C E F hE hF Q' R).hom ≫
      (derivedBimoduleComposeFunctor A B C F hF).map
        (((derivedBimoduleComposeFunctor A C E F hF).map g).app Q') at hR
  change (_ ≫ _) ≫ _ = _ ≫ (derivedBimoduleComposeFunctor A B C F hF).map (_ ≫ _)
  rw [Category.assoc, hR, ← Category.assoc, hQ, Category.assoc,
    ← CategoryTheory.Functor.map_comp]

end SerrePositivity.DifferentialGraded.BimoduleTensor
