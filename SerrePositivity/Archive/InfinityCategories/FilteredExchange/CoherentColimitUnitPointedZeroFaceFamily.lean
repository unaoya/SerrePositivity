module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitPointedUniversalLift
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitPointedFaceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedTransportPrismFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.WitnessPushoutContractible

/-!
概要：元の単位三単体の第零面を、元の全選択で初期値が動く pointed 延長族にする。
方針：全三単体の普遍的な持ち上げの頂点一で境界を取り、第零面の底を保つ。
規約：初期値を F に固定しない。使われ方：第一辺による前合成と指定比較の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3)

/-- 元の第零面の始点は頂点一における実持ち上げであり、全選択とともに動く。 -/
def coherentColimitUnitPointedZeroFaceFamily :
    PointedTransportPrismFamily
      (K := coherentColimitUnitPointedTetrahedronChoice B T k)
      (scaffoldFirstVertex 2) (leftUnstraighteningProjection F) where
  diagram := fst (Δ[2] ⊗ (SSet.uliftFunctor.{u + 1, u}).obj B) _ ≫
    functorSimplexDiagram (SSet.yonedaEquiv.symm
      (((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
        (coherentColimitUnitTriangleTetrahedron B T k)))
  boundary := (((scaffoldFirstVertex 2 ≫ stdSimplex.δ (0 : Fin 4)) ▷
    leftUnstraightening F) ▷ _) ≫ coherentColimitUnitPointedTetrahedronUniversalLift B T k
  projection := by
    rw [Category.assoc, coherentColimitUnitPointedTetrahedronUniversalLift_projection]
    rw [← coherentColimitUnitPointedTetrahedronDiagram_face B T k 0 _
      (Equiv.apply_symm_apply SSet.yonedaEquiv _).symm]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- 可変初期値の第零面の延長は、元の全選択への trivial Kan fibration をなす。 -/
lemma coherentColimitUnitPointedZeroFaceFamily_trivialKanFibration :
    TrivialKanFibration (coherentColimitUnitPointedZeroFaceFamily B T k).liftSpaceProjection :=
  (coherentColimitUnitPointedZeroFaceFamily B T k).liftSpaceProjection_trivialKanFibration
    (scaffoldFirstVertex_leftAnodyne 2)

/-- 初期値を変動させたまま、第零面の全選択を元の全選択と束ねた空間は可縮。 -/
lemma coherentColimitUnitPointedZeroFaceFamily_contractible :
    IsContractibleKan (coherentColimitUnitPointedZeroFaceFamily B T k).liftSpace := by
  have := coherentColimitUnitPointedZeroFaceFamily_trivialKanFibration B T k
  exact isContractibleKan_of_trivialKanFibration
    (coherentColimitUnitPointedZeroFaceFamily B T k).liftSpaceProjection
    (coherentColimitUnitPointedTetrahedronChoice_contractible B T k)

end SerrePositivity.InfinityCategories.F2
