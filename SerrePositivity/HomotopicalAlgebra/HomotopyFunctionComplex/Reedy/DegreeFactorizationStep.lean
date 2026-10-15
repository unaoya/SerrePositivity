module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeExtension

/-! # Extending an actual diagram factorization to the next closed degree

This returns a factorization of the original natural transformation on the
ordinary degree restriction, rather than only of reconstructed diagrams on
the auxiliary attached category.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy.DegreeFactorizationStep
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J) (hinj : Function.Injective r.deg)
  {C : Type u'} [Category.{v'} C]
  [HasColimitsOfShape (LatchingIndex r j) C] [HasLimitsOfShape (MatchingIndex r j) C]
  [HasPushouts C] [HasPullbacks C]
  {F G : J ⥤ C} (τ : F ⟶ G)
  {lowerLeft lowerRight : MorphismProperty (Lower r (r.deg j) ⥤ C)}
  (a : MorphismProperty.MapFactorizationData lowerLeft lowerRight
    (Functor.whiskerLeft (lowerInclusion r (r.deg j)) τ))
  {left right : MorphismProperty C}
  (q : MorphismProperty.MapFactorizationData left right
    (RelativeExtension.map (BoundaryExtension.mapOfNatTrans r j τ) a))

abbrev middle : Upper r (r.deg j) ⥤ C :=
  (RelativeExtension.extension (BoundaryExtension.mapOfNatTrans r j τ) a q).degreeExtension hinj

abbrev leftMap : upperInclusion r (r.deg j) ⋙ F ⟶ middle r j hinj τ a q :=
  (BoundaryExtension.degreeOfFunctorIso r j F hinj).inv ≫
    Functor.whiskerLeft (degreeIndex r j hinj)
      (RelativeExtension.leftMap (BoundaryExtension.mapOfNatTrans r j τ) a q).toNatTrans

abbrev rightMap : middle r j hinj τ a q ⟶ upperInclusion r (r.deg j) ⋙ G :=
  Functor.whiskerLeft (degreeIndex r j hinj)
      (RelativeExtension.rightMap (BoundaryExtension.mapOfNatTrans r j τ) a q).toNatTrans ≫
    (BoundaryExtension.degreeOfFunctorIso r j G hinj).hom

lemma leftMap_rightMap : leftMap r j hinj τ a q ≫ rightMap r j hinj τ a q =
    Functor.whiskerLeft (upperInclusion r (r.deg j)) τ := by
  have hc :
      Functor.whiskerLeft (degreeIndex r j hinj)
          (RelativeExtension.leftMap (BoundaryExtension.mapOfNatTrans r j τ) a q).toNatTrans ≫
        Functor.whiskerLeft (degreeIndex r j hinj)
          (RelativeExtension.rightMap (BoundaryExtension.mapOfNatTrans r j τ) a q).toNatTrans =
      Functor.whiskerLeft (degreeIndex r j hinj)
        (BoundaryExtension.mapOfNatTrans r j τ).toNatTrans := by
    ext x
    exact congr_app (RelativeExtension.leftMap_rightMap
      (BoundaryExtension.mapOfNatTrans r j τ) a q) ((degreeIndex r j hinj).obj x)
  unfold leftMap rightMap
  rw [Category.assoc, ← Category.assoc _ _ (BoundaryExtension.degreeOfFunctorIso r j G hinj).hom,
    hc, BoundaryExtension.degreeOfFunctorIso_naturality, Iso.inv_hom_id_assoc]

abbrev factorizationData : MorphismProperty.MapFactorizationData ⊤ ⊤
    (Functor.whiskerLeft (upperInclusion r (r.deg j)) τ) where
  Z := middle r j hinj τ a q
  i := leftMap r j hinj τ a q
  p := rightMap r j hinj τ a q
  fac := leftMap_rightMap r j hinj τ a q
  hi := trivial
  hp := trivial

abbrev restrictionIso : lowerToUpper r j ⋙ middle r j hinj τ a q ≅ a.Z :=
  (RelativeExtension.extension (BoundaryExtension.mapOfNatTrans r j τ) a q).degreeRestrictionIso hinj

end SerrePositivity.Reedy.DegreeFactorizationStep
