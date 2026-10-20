module

public import SerrePositivity.InfinityCategories.F1.RelativeHomPointedRecoveryTransport
public import SerrePositivity.InfinityCategories.F1.LeftIntervalEquivalence
public import SerrePositivity.InfinityCategories.F1.PointFunctorEvaluation

/-!
概要：元の Kan 空間から実際の pointed fiber への、右 Hom の恒等点輸送による比較。
方針：一点 coslice の恒等射を大域射として使い、区間評価の同値性を fiber 上の恒等則から示す。
規約：元の右 Hom と既存の区間輸送を使い、Kan 空間とその反転を同一視しない。
使われ方：元の coherent な恒等点回収を、同じ pointed fiber への比較へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 一点空間上の恒等錐を、元の pointed-space の fiber の指定点として表す。 -/
def pointedSpaceIdentityPoint :
    (vertexFiber pointedSpaceProjection pointSpaceVertex.{u}) _⦋0⦌ :=
  ⟨cosliceIdentityCone pointSpaceVertex, by
    rw [PinchedHom.constant_zero]
    exact cosliceIdentityCone_projection pointSpaceVertex⟩

/-- 一点空間からの元の全区間族で、同じ恒等錐の点を輸送する。 -/
def pointedRightIntervalEvaluate (s : SpaceInfinity.{u} _⦋0⦌) :
    intervalMappingSpace pointSpaceVertex s ⟶ vertexFiber pointedSpaceProjection s :=
  diagonalFiberTransport pointedSpaceProjection (SSet.const pointedSpaceIdentityPoint) (𝟙 _)

/-- 一点 coslice 全体の恒等射の fiber 作用により、元の区間評価そのものは同値。 -/
lemma pointedRightIntervalEvaluate_isQCatEquivalence (s : SpaceInfinity.{u} _⦋0⦌) :
    IsQCatEquivalence (pointedRightIntervalEvaluate s) := by
  have e := leftFibrationCosliceMap_transportIso pointedSpaceProjection
    pointSpaceVertex (cosliceIdentityCone pointSpaceVertex)
    (cosliceIdentityCone_projection pointSpaceVertex) (𝟙 _)
    (Category.id_comp pointedSpaceProjection) (by rfl) s
  change FunctorIso
    (vertexFiberMap pointedSpaceProjection pointedSpaceProjection (𝟙 PointedSpaceInfinity.{u})
      (Category.id_comp pointedSpaceProjection) s)
    (diagonalFiberTransport pointedSpaceProjection (SSet.const pointedSpaceIdentityPoint)
      (cosliceFiberToIntervalMappingSpace pointSpaceVertex s)) at e
  rw [vertexFiberMap_id] at e
  have h : cosliceFiberToIntervalMappingSpace pointSpaceVertex s ≫
      pointedRightIntervalEvaluate s =
      diagonalFiberTransport pointedSpaceProjection (SSet.const pointedSpaceIdentityPoint)
        (cosliceFiberToIntervalMappingSpace pointSpaceVertex s) := by
    rw [pointedRightIntervalEvaluate, diagonalFiberTransport_precomp,
      SSet.comp_const, Category.comp_id]
  apply (cosliceFiberToIntervalMappingSpace_isQCatEquivalence pointSpaceVertex s).cancel_left
  rw [h]
  exact (qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence.ofFunctorIso e

/-- 恒等射による区間空間の端点表示変更は、元の射そのものが厳密な同型。 -/
lemma intervalMappingPostOfEq_id_isIso {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') :
    IsIso (intervalMappingPostOfEq (𝟙 X) x y hx hy) := by
  subst x'
  subst y'
  have h : intervalMappingPostOfEq (𝟙 X) x y rfl rfl = 𝟙 (intervalMappingSpace x y) := by
    apply intervalMappingUncurry_injective x y
    simpa only [Category.id_comp, Category.comp_id] using
      intervalMappingPostOfEq_uncurry (𝟙 X) x y rfl rfl (𝟙 (intervalMappingSpace x y))
  rw [h]
  infer_instance

/-- 元の Kan 空間を、右 Hom の恒等点輸送で実際の pointed fiber へ比較する。 -/
def pointedRightFiberComparison (K : KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj K.obj ⟶
      vertexFiber pointedSpaceProjection (spaceInfinityVertex K) :=
  (SSet.uliftFunctor.{u + 1, u}).map (pointFunctorEvaluationIso K.obj).inv ≫
    coherentHomComparison pointKanObject K ≫
    pinchedHomToIntervalMappingSpace (coherentNerveVertex pointKanObject) (coherentNerveVertex K) ≫
    intervalMappingPostOfEq (𝟙 SpaceInfinity.{u})
      (coherentNerveVertex pointKanObject) (coherentNerveVertex K)
      (spaceInfinityVertex_eq_coherent pointKanObject).symm
      (spaceInfinityVertex_eq_coherent K).symm ≫
    pointedRightIntervalEvaluate (spaceInfinityVertex K)

/-- 右 Hom の同じ恒等点輸送による比較は、元の Kan 空間全体で同値。 -/
lemma pointedRightFiberComparison_isQCatEquivalence (K : KanObject.{u}) :
    IsQCatEquivalence (pointedRightFiberComparison K) := by
  have h₀ := (qCatEquivalenceOfIso
    ((SSet.uliftFunctor.{u + 1, u}).mapIso
      (pointFunctorEvaluationIso K.obj).symm)).isQCatEquivalence
  have h₁ := coherentHomComparison_isQCatEquivalence pointKanObject K
  have h₂ := pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (coherentNerveVertex pointKanObject) (coherentNerveVertex K)
  have : IsIso (intervalMappingPostOfEq (𝟙 SpaceInfinity.{u})
      (coherentNerveVertex pointKanObject) (coherentNerveVertex K)
      (spaceInfinityVertex_eq_coherent pointKanObject).symm
      (spaceInfinityVertex_eq_coherent K).symm) :=
    intervalMappingPostOfEq_id_isIso (X := SpaceInfinity.{u})
      (spaceInfinityVertex_eq_coherent pointKanObject).symm
      (spaceInfinityVertex_eq_coherent K).symm
  have h₃ := (qCatEquivalenceOfIso (asIso
    (intervalMappingPostOfEq (𝟙 SpaceInfinity.{u})
      (coherentNerveVertex pointKanObject) (coherentNerveVertex K)
      (spaceInfinityVertex_eq_coherent pointKanObject).symm
      (spaceInfinityVertex_eq_coherent K).symm))).isQCatEquivalence
  exact h₀.comp (h₁.comp (h₂.comp (h₃.comp
    (pointedRightIntervalEvaluate_isQCatEquivalence (spaceInfinityVertex K)))))

end SerrePositivity.InfinityCategories
