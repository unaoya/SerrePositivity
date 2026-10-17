module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSecondFactor
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSemifreeIndependence
public import SerrePositivity.DifferentialGraded.Derived.BimoduleSemifreeLift

/-! # 指定semifree解像度と標準解像度による中間圏導来比較の後因子自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)

lemma middleRestrictionResolvedMap_semifree_second_naturality
    (P : BimoduleCategory A B C) {Q Q' : BimoduleCategory A C E} (g : Q ⟶ Q')
    (R : BimoduleSemifreeResolution A D E
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q))
    (S : BimoduleSemifreeResolution A D E
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q')) :
    (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P))))
      (R.lift A D E S (BimoduleCategory.middleRightRestrictionMap A C D E F g))) ≫
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q' S.obj S.π) =
    (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q R.obj R.π) ≫
      (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) g) := by
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P
  let T := bimoduleToDerived A B E
  have hc := BimoduleSemifreeResolution.composeAfter_lift_fac A D E B P₀ R S
    (BimoduleCategory.middleRightRestrictionMap A C D E F g)
  have hr : composeMap A B D E (𝟙 P₀)
        (BimoduleCategory.middleRightRestrictionMap A C D E F g) ≫
      middleRestrictionComparisonMap A B C D E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q') =
    middleRestrictionComparisonMap A B C D E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) ≫
      composeMap A B C E (𝟙 P) g :=
    middleRestrictionComparisonMap_naturality A B C D E F (𝟙 P) g
  have hn := congrArg T.map hr
  rw [T.map_comp, T.map_comp] at hn
  dsimp only [middleRestrictionResolvedMap]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ T.map (middleRestrictionComparisonMap A B C D E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q'))) hc).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => T.map (composeMap A B D E (𝟙 P₀) R.π) ≫ k) hn).trans
          (Category.assoc _ _ _).symm)))

lemma derivedMiddleRestrictionComparison_semifree_second_naturality (hE : localHomKFlat A E)
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q')
    (R : BimoduleSemifreeResolution A D E
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))
    (S : BimoduleSemifreeResolution A D E
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q'.obj))
    (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B D E hE).map ((bimoduleToDerived A D E).map
        (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom))).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P)) ≫
      derivedMiddleRestrictionComparison A B C D E F hE P Q'
        (S.toRightKFlat A D E hE) S.π S.quasiIso =
    derivedMiddleRestrictionComparison A B C D E F hE P Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso ≫
      ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom)).app
        ((bimoduleToDerived A B C).obj P) := by
  let r : R.toRightKFlat A D E hE ⟶ S.toRightKFlat A D E hE := ObjectProperty.homMk
    (R.lift A D E S (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom))
  exact derivedMiddleRestrictionComparison_second_naturality_of_squares A B C D E F hE g
    (R.toRightKFlat A D E hE) (S.toRightKFlat A D E hE) R.π S.π R.quasiIso S.quasiIso r
    (R.lift_fac A D E S (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom)).symm P
    (middleRestrictionResolvedMap_semifree_second_naturality A B C D E F P g.hom R S)

/-- 標準解像度による実際の導来比較は、任意の右K-flat後因子の射に対して自然。 -/
lemma derivedMiddleRestrictionCanonicalComparison_second_naturality (hE : localHomKFlat A E)
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B D E hE).map ((bimoduleToDerived A D E).map
        (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom))).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P)) ≫
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q' =
    derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q ≫
      ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom)).app
        ((bimoduleToDerived A B C).obj P) :=
  derivedMiddleRestrictionComparison_semifree_second_naturality A B C D E F hE g
    (bimoduleCanonicalSemifreeResolution A D E _)
    (bimoduleCanonicalSemifreeResolution A D E _) P

end SerrePositivity.DifferentialGraded.BimoduleTensor
