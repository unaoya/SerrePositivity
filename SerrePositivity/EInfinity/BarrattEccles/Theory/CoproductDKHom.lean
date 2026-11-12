module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoproductMappingSpace
public import SerrePositivity.EInfinity.BarrattEccles.Theory.NativeCoproductCocone
public import SerrePositivity.EInfinity.BarrattEccles.KanDKMappingSpaceNaturality
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne

/-!
# 実際の Kan DK Hom の余積比較

概要：HA 3.2.4.7 の二つの指定包含による全 Hom の積比較を示す。
方針：Map^h の積比較を ULift し、前合成に自然な DK 比較で移す。
規約：π₀ の比較に置き換えず、元の Ex∞ と二包含を使う。
使われ方：native な二項余積錐の余極限性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SimplicialLocalization
open SerrePositivity.SimplicialModel SerrePositivity.KST.Comparison
variable (A : Type u) [CommRing A]
  (X Y Z : CAlgSimplicialCategory A)

/-- ULift の二項積保存を次数評価で確認する。 -/
instance simplicialUlift_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) SSet.uliftFunctor.{u + 1, u} := by
  apply preservesLimitsOfShape_of_evaluation
  intro n
  change PreservesLimitsOfShape (Discrete WalkingPair)
    ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n ⋙ CategoryTheory.uliftFunctor.{u + 1, u})
  infer_instance

/-- 同じ厳密余積の二包含が誘導する実際の Kan Hom の積比較。 -/
def cAlgCoprodHomRestriction :
    SimplicialCategory.sHom
      (show CAlgSimplicialCategory A from (cofibrantAlgebraDKCoprodWith A Y).obj X) Z ⟶
      SimplicialCategory.sHom X Z ⨯ SimplicialCategory.sHom Y Z :=
  prod.lift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (localizationPrecompose (cofibrantAlgebraRelativeCategory A) Z
      (cofibrantAlgebraDKCoprodInl A X Y)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (localizationPrecompose (cofibrantAlgebraRelativeCategory A) Z
      (cofibrantAlgebraDKCoprodInr A X Y)))

/-- 実際の Kan Hom の積比較は anodyne 局所化で同型。 -/
lemma cAlgCoprodHomRestriction_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (cAlgCoprodHomRestriction A X Y Z)) := by
  let := modelCategory A
  let U := SSet.uliftFunctor.{u + 1, u}
  let Q := AnodyneHomotopy.anodyneQ
  let j := cofibrantAlgebraDKInclusion A
  let T : CAlgSimplicialCategory A := (cofibrantAlgebraDKCoprodWith A Y).obj X
  let B := fun W => ((mappingSpace A).obj (op (j.obj W))).obj (j.obj Z)
  have hX := cofibrantAlgebra_isCofibrant A X
  have hY := cofibrantAlgebra_isCofibrant A Y
  have hr := mappingSpaceCoprodRestriction_isIso A (j.obj X) (j.obj Y) (j.obj Z) hX hY
  have hu := UniverseLift.anodyneQ_map_isIso_of_small.{u + 1, u}
    (mappingSpaceCoprodRestriction A (j.obj X) (j.obj Y) (j.obj Z)) hr
  let r := U.map (mappingSpaceCoprodRestriction A (j.obj X) (j.obj Y) (j.obj Z)) ≫
    prodComparison U (B X) (B Y)
  have : IsIso (Q.map r) := by
    dsimp [r]
    rw [Functor.map_comp]
    infer_instance
  let e := fun W => cAlgMappingSpaceComparisonIso A W Z
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (localizationPrecompose (cofibrantAlgebraRelativeCategory A) Z
    (cofibrantAlgebraDKCoprodInl A X Y))
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (localizationPrecompose (cofibrantAlgebraRelativeCategory A) Z
    (cofibrantAlgebraDKCoprodInr A X Y))
  let f' := U.map (((mappingSpace A).map
    (coprod.inl : j.obj X ⟶ j.obj X ⨿ j.obj Y).op).app (j.obj Z))
  let g' := U.map (((mappingSpace A).map
    (coprod.inr : j.obj Y ⟶ j.obj X ⨿ j.obj Y).op).app (j.obj Z))
  have hr' : r = prod.lift f' g' := mapPairing_prodComparison U _ _
  have hf : Q.map f ≫ (e X).hom = (e T).hom ≫ Q.map f' :=
    cAlgMappingSpaceComparisonIso_precompose A Z (cofibrantAlgebraDKCoprodInl A X Y)
  have hg : Q.map g ≫ (e Y).hom = (e T).hom ≫ Q.map g' :=
    cAlgMappingSpaceComparisonIso_precompose A Z (cofibrantAlgebraDKCoprodInr A X Y)
  have he : Q.map (cAlgCoprodHomRestriction A X Y Z) ≫
      prodComparison Q (SimplicialCategory.sHom X Z) (SimplicialCategory.sHom Y Z) ≫
        prod.map (e X).hom (e Y).hom =
    (e T).hom ≫ Q.map r ≫ prodComparison Q (U.obj (B X)) (U.obj (B Y)) := by
    change Q.map (prod.lift f g) ≫ _ ≫ _ = _
    calc
      _ = prod.lift (Q.map f ≫ (e X).hom) (Q.map g ≫ (e Y).hom) := by
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ prod.map (e X).hom (e Y).hom)
            (mapPairing_prodComparison Q f g)).trans (prod.lift_map _ _ _ _))
      _ = prod.lift ((e T).hom ≫ Q.map f') ((e T).hom ≫ Q.map g') := by rw [hf, hg]
      _ = (e T).hom ≫ prod.lift (Q.map f') (Q.map g') := (prod.comp_lift _ _ _).symm
      _ = _ := by
        rw [hr']
        exact congrArg (fun t => (e T).hom ≫ t) (mapPairing_prodComparison Q f' g').symm
  have hi : IsIso (Q.map (cAlgCoprodHomRestriction A X Y Z) ≫
      prodComparison Q (SimplicialCategory.sHom X Z) (SimplicialCategory.sHom Y Z) ≫
        prod.map (e X).hom (e Y).hom) := by rw [he]; infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

end SerrePositivity.EInfinity.BarrattEccles
