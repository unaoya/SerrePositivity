module
public import SerrePositivity.DifferentialGraded.Derived.CompositionFamilies
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagonKFlat

/-! # 任意のパラメータ圏上の導来bimodule合成と結合比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t x s s'
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]
variable {T : Type s} [Category.{s'} T]

omit [DGCategory A B] [Small.{u} B] [DGCategory A G] [Small.{u} G] in
def derivedBimoduleComposeFamily (hF : localHomKFlat A F)
    (Q : T ⥤ DerivedBimoduleCategory A C E) (R : T ⥤ DerivedBimoduleCategory A E F) :
    T ⥤ DerivedBimoduleCategory A C F :=
  Q.prod' (R ⋙ derivedBimoduleComposeFunctor A C E F hF) ⋙
    evaluationUncurried (DerivedBimoduleCategory A C E) (DerivedBimoduleCategory A C F)

omit [DGCategory A G] [Small.{u} G] in
def derivedBimoduleAssociatorFamily (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    (Q : T ⥤ DerivedBimoduleCategory A C E) (R : T ⥤ DerivedBimoduleCategory A E F) :
    compositionFamily (Q ⋙ derivedBimoduleComposeFunctor A B C E hE)
        (R ⋙ derivedBimoduleComposeFunctor A B E F hF) ≅
      derivedBimoduleComposeFamily A C E F hF Q R ⋙ derivedBimoduleComposeFunctor A B C F hF :=
  NatIso.ofComponents
    (fun t => derivedBimoduleAssociator A B C E F hE hF (Q.obj t) (R.obj t))
    (fun f => derivedBimoduleAssociator_naturality A B C E F hE hF (Q.map f) (R.map f))

omit [DGCategory A B] [Small.{u} B] in
def derivedBimoduleInnerAssociatorFamily (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : T ⥤ DerivedBimoduleCategory A C E) (R : T ⥤ DerivedBimoduleCategory A E F)
    (S : T ⥤ DerivedBimoduleCategory A F G) :
    derivedBimoduleComposeFamily A C F G hG (derivedBimoduleComposeFamily A C E F hF Q R) S ≅
      derivedBimoduleComposeFamily A C E G hG Q (derivedBimoduleComposeFamily A E F G hG R S) :=
  NatIso.ofComponents
    (fun t => (derivedBimoduleAssociator A C E F G hF hG (R.obj t) (S.obj t)).app (Q.obj t))
    (fun {i j} f => by
      have hQ := (derivedBimoduleAssociator A C E F G hF hG (R.obj i) (S.obj i)).hom.naturality
        (Q.map f)
      simp only [Functor.comp_map] at hQ
      have hRS := NatTrans.congr_app
        (derivedBimoduleAssociator_naturality A C E F G hF hG (R.map f) (S.map f)) (Q.obj j)
      simp only [derivedBimoduleComposePairMap, NatTrans.comp_app, whiskerRight_app,
        whiskerLeft_app, Category.assoc] at hRS
      change
        (((derivedBimoduleComposeFunctor A C F G hG).obj (S.obj i)).map
          (((derivedBimoduleComposeFunctor A C E F hF).obj (R.obj i)).map (Q.map f) ≫
            ((derivedBimoduleComposeFunctor A C E F hF).map (R.map f)).app (Q.obj j)) ≫
          ((derivedBimoduleComposeFunctor A C F G hG).map (S.map f)).app
            (((derivedBimoduleComposeFunctor A C E F hF).obj (R.obj j)).obj (Q.obj j))) ≫
          (derivedBimoduleAssociator A C E F G hF hG (R.obj j) (S.obj j)).hom.app (Q.obj j) =
        (derivedBimoduleAssociator A C E F G hF hG (R.obj i) (S.obj i)).hom.app (Q.obj i) ≫
          (((derivedBimoduleComposeFunctor A C E G hG).obj
            (((derivedBimoduleComposeFunctor A E F G hG).obj (S.obj i)).obj (R.obj i))).map
              (Q.map f) ≫
            ((derivedBimoduleComposeFunctor A C E G hG).map
              (derivedBimoduleComposeInnerMap A E F G hG (R.map f) (S.map f))).app (Q.obj j))
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rw [hRS]
      rw [← Category.assoc, hQ, Category.assoc])

end SerrePositivity.DifferentialGraded.BimoduleTensor
