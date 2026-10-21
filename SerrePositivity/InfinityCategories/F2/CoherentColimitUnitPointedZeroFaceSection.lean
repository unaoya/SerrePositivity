module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitPointedZeroFaceFamily
public import SerrePositivity.InfinityCategories.F2.PointedPrismFamilySection

/-!
概要：元の三単体の実際の第零面を、可変初期値の全選択空間の切断にする。
方針：元の普遍的持ち上げを制限し、そのまま全延長族へ束ねる。
規約：元の全パラメータを保持。使われ方：第一辺と第零面の初期値の厳密な照合。
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

/-- 元の全三単体の全選択を、その実際の第零面に制限した全持ち上げ。 -/
def coherentColimitUnitPointedZeroFaceLift :=
  ((stdSimplex.δ (0 : Fin 4) ▷ leftUnstraightening F) ▷
    coherentColimitUnitPointedTetrahedronChoice B T k) ≫
      coherentColimitUnitPointedTetrahedronUniversalLift B T k

/-- 第零面の実制限は、頂点一の可変初期値を厳密に保つ。 -/
lemma coherentColimitUnitPointedZeroFaceLift_boundary :
    ((scaffoldFirstVertex 2 ▷ leftUnstraightening F) ▷
      coherentColimitUnitPointedTetrahedronChoice B T k) ≫
        coherentColimitUnitPointedZeroFaceLift B T k =
          (coherentColimitUnitPointedZeroFaceFamily B T k).boundary := by
  rw [coherentColimitUnitPointedZeroFaceLift, ← Category.assoc,
    ← comp_whiskerRight, ← comp_whiskerRight]
  rfl

/-- 第零面の実制限は、元の全底図式を全選択で厳密に被覆する。 -/
lemma coherentColimitUnitPointedZeroFaceLift_projection :
    coherentColimitUnitPointedZeroFaceLift B T k ≫ pointedSpaceProjection =
      ((Δ[2] ◁ leftUnstraighteningProjection F) ▷
        coherentColimitUnitPointedTetrahedronChoice B T k) ≫
          (coherentColimitUnitPointedZeroFaceFamily B T k).diagram := by
  rw [coherentColimitUnitPointedZeroFaceLift, Category.assoc,
    coherentColimitUnitPointedTetrahedronUniversalLift_projection]
  change _ = _ ≫ fst _ _ ≫ functorSimplexDiagram _
  rw [← coherentColimitUnitPointedTetrahedronDiagram_face B T k 0 _
    (Equiv.apply_symm_apply SSet.yonedaEquiv _).symm]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の第零面の実制限を、そのまま可変初期値の全延長空間へ束ねる切断。 -/
def coherentColimitUnitPointedZeroFaceSection :=
  pointedPrismFamilySection (coherentColimitUnitPointedZeroFaceFamily B T k)
    (coherentColimitUnitPointedZeroFaceLift B T k)
    (coherentColimitUnitPointedZeroFaceLift_boundary B T k)
    (coherentColimitUnitPointedZeroFaceLift_projection B T k)

/-- 元の実制限の切断は、元の全三単体の全選択を厳密に保持する。 -/
lemma coherentColimitUnitPointedZeroFaceSection_projection :
    coherentColimitUnitPointedZeroFaceSection B T k ≫
      (coherentColimitUnitPointedZeroFaceFamily B T k).liftSpaceProjection = 𝟙 _ :=
  pointedPrismFamilySection_projection _ _ _ _

end SerrePositivity.InfinityCategories.F2
