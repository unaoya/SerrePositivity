module

public import SerrePositivity.InfinityCategories.F1.Categories.OppositeUnstraighteningHomFamilies

/-!
概要：全 Hom パラメーターの反転変換の作用を、元の weighted 始域上の実際の prism で表す。
方針：普遍的な unstraightening の持ち上げを元の比較と同じ区間パラメーターで制限する。
規約：始点・終点・底を全パラメーターで固定する。
使われ方：自然性四角形の右側の実現と、weighted な左側の実現の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {I : Type u} [SmallCategory I] (F G : KanDiagramObject I)

/-- 元の weighted 始域上の、全反転変換の実際の底の prism。 -/
def oppositeUnstraighteningHomBase :
    ((Δ[1] : SSet.{u + 1}) ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve (F.val ⋙ kanObjectForget))) ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj
        (edgewiseSubdivision (SimplicialCategory.sHom F G)) ⟶ SpaceInfinity.{u} :=
  ((Δ[1] ◁ (SSet.uliftFunctor.{u + 1, u}).map
    (weightedNerveProjection (F.val ⋙ kanObjectForget))) ▷ _) ≫
    functorParameterizedPrism (intervalMappingUncurry (kanDiagramOppositeHomInterval F G))

/-- 同じ反転変換の普遍持ち上げを元の weighted 始域と全 Hom で同時に制限する。 -/
def oppositeUnstraighteningHomPrism :
    ((Δ[1] : SSet.{u + 1}) ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve (F.val ⋙ kanObjectForget))) ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj
        (edgewiseSubdivision (SimplicialCategory.sHom F G)) ⟶ PointedSpaceInfinity.{u} :=
  ((Δ[1] ◁ oppositeKanUnstraighteningComparison F.val) ⊗ₘ
    kanDiagramOppositeHomInterval F G) ≫
    leftUnstraighteningTransformationFamilyLift
      (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))
      (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor))

/-- この同じ prism の始点は、元の始域比較の pointed 成分を全 Hom 上で固定した族。 -/
lemma oppositeUnstraighteningHomPrism_zero :
    (prismEndpoint 0 ((SSet.uliftFunctor.{u + 1, u}).obj
      (weightedNerve (F.val ⋙ kanObjectForget))) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj
        (edgewiseSubdivision (SimplicialCategory.sHom F G))) ≫
      oppositeUnstraighteningHomPrism F G =
    fst _ _ ≫ oppositeKanUnstraighteningComparison F.val ≫ pullback.fst pointedSpaceProjection
      (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  exact congrArg (fun k => k.app n
    ((oppositeKanUnstraighteningComparison F.val).app n x,
      (kanDiagramOppositeHomInterval F G).app n t))
    (leftUnstraighteningTransformationFamilyLift_start
      (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))
      (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)))

/-- この同じ prism の終点は、全相対射上の右端の実際の pointed 成分。 -/
lemma oppositeUnstraighteningHomPrism_one :
    (prismEndpoint 1 ((SSet.uliftFunctor.{u + 1, u}).obj
      (weightedNerve (F.val ⋙ kanObjectForget))) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj
        (edgewiseSubdivision (SimplicialCategory.sHom F G))) ≫
      oppositeUnstraighteningHomPrism F G =
    relativeFunctorUncurry (oppositeUnstraighteningHomRight F G) ≫
      pullback.fst pointedSpaceProjection
        (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)) := by
  rw [oppositeUnstraighteningHomRight_uncurry, relativeFunctorUncurry_naturality,
    Category.assoc, Category.assoc, leftUnstraighteningMappingSpaceMap_pointed]
  apply SSet.hom_ext
  intro n
  rfl

/-- この同じ prism は、元の底射影と反転変換の全区間族を厳密に被覆する。 -/
lemma oppositeUnstraighteningHomPrism_projection :
    oppositeUnstraighteningHomPrism F G ≫ pointedSpaceProjection =
      oppositeUnstraighteningHomBase F G := by
  let P := (SSet.uliftFunctor.{u + 1, u}).obj
    (edgewiseSubdivision (SimplicialCategory.sHom F G))
  let T := leftUnstraighteningTransformationSpace
    (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))
    (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor))
  have h : ((Δ[1] ◁ oppositeKanUnstraighteningComparison F.val) ⊗ₘ
      kanDiagramOppositeHomInterval F G) ≫
      ((Δ[1] ◁ leftUnstraighteningProjection
        (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))) ▷ T) =
      ((Δ[1] ◁ (SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveProjection (F.val ⋙ kanObjectForget))) ▷ P) ≫
      ((Δ[1] ⊗ (SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) ◁
        kanDiagramOppositeHomInterval F G) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, x⟩, t⟩
    exact congrArg (fun z => ((a, z), (kanDiagramOppositeHomInterval F G).app n t))
      (congrArg (fun k => k.app n x) (oppositeKanUnstraighteningComparison_projection F.val))
  rw [oppositeUnstraighteningHomPrism, Category.assoc,
    leftUnstraighteningTransformationFamilyLift_projection, ← Category.assoc, h,
    Category.assoc, leftUnstraighteningTransformationFamily_parameter]
  rfl

end SerrePositivity.InfinityCategories
