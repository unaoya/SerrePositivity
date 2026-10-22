module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconePathSpaceLimit
public import SerrePositivity.InfinityCategories.F2.SpaceSquareProjections

/-! 空間の ∞ 極限錐の二つの脚は、元の path 写像と cocone 射影の厳密な辺。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded CochainComplex
open F2
variable {R : Type u} [CommRing R] {P Q : Complex R} (d : P ⟶ Q)

lemma dgGluingCoconePathSpaceCone_path :
    (nativeConeLeg (dgGluingCoconePathSpaceCone.{u, v} d)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.left)))).edge =
      (coherentNerveEdge
        (show dgGluingComplexPinchedKanObject.{u, v} (mappingCocone d) ⟶
          dgGluingComplexPinchedKanObject.{u, v} (mappingCocone (𝟙 Q)) from
          complexPinchedMap.{u, v} (dgGluingCoconePathMap d))).edge :=
  spaceSquareCone_left _ _ _ _ _

lemma dgGluingCoconePathSpaceCone_base :
    (nativeConeLeg (dgGluingCoconePathSpaceCone.{u, v} d)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.right)))).edge =
      (coherentNerveEdge
        (show dgGluingComplexPinchedKanObject.{u, v} (mappingCocone d) ⟶
          dgGluingComplexPinchedKanObject.{u, v} P from
          complexPinchedMap.{u, v} (mappingCocone.fst d))).edge :=
  spaceSquareCone_right _ _ _ _ _

end SerrePositivity.InfinityCategories
