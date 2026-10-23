module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowCompositionPullback
public import SerrePositivity.InfinityCategories.F2.CatInfinity.SpaceSquareLimits

/-! 同じ二合成対応の対角引き戻しを頂点とする、空間の実 ∞ 極限錐。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
variable {X : SSet.{u}} [Quasicategory X] {a b c d : X _⦋0⦌}
  (f : X.Edge a b) (g : X.Edge c d)

def dgGluingFirstCompositionKanObject : KanObject.{u} :=
  ⟨dgGluingFirstFixedCompositionSpace f d, dgGluingFirstFixedCompositionSpace_kanComplex f d⟩

def dgGluingLastCompositionKanObject : KanObject.{u} :=
  ⟨compositionCorrespondence a g, compositionCorrespondence_kanComplex a g⟩

def dgGluingCompositionDiagonalKanObject : KanObject.{u} :=
  ⟨intervalMappingSpace a d, inferInstance⟩

def dgGluingArrowCompositionKanObject : KanObject.{u} :=
  ⟨dgGluingArrowCompositionPullback f g, dgGluingArrowCompositionPullback_kanComplex f g⟩

def dgGluingFirstCompositionKanMap :
    dgGluingFirstCompositionKanObject f (d := d) ⟶
      dgGluingCompositionDiagonalKanObject (a := a) (d := d) :=
  dgGluingFirstFixedCompositionDiagonal f d

def dgGluingLastCompositionKanMap :
    dgGluingLastCompositionKanObject (a := a) g ⟶
      dgGluingCompositionDiagonalKanObject (a := a) (d := d) :=
  compositionCorrespondenceDiagonal a g

def dgGluingArrowCompositionDiagram : AsSmall.{u} WalkingCospan ⥤ KanObject.{u} :=
  HomotopyLimits.kanPullbackDiagram (dgGluingLastCompositionKanMap (a := a) g)
    (dgGluingFirstCompositionKanMap (d := d) f)

def dgGluingArrowCompositionCone :
    JoinCone (kanDiagramCoherentNerve (dgGluingArrowCompositionDiagram f g)) :=
  F2.spaceSquareCone (K := dgGluingArrowCompositionKanObject f g)
    (dgGluingLastCompositionKanMap (a := a) g) (dgGluingFirstCompositionKanMap (d := d) f)
    (pullback.snd _ _) (pullback.fst _ _)
    (IsPullback.of_hasPullback (dgGluingFirstFixedCompositionDiagonal f d)
      (compositionCorrespondenceDiagonal a g)).flip

lemma dgGluingArrowCompositionCone_isLimit : IsLimitCone (dgGluingArrowCompositionCone f g) := by
  let : Fibration (show (dgGluingLastCompositionKanObject (a := a) g).obj ⟶
      (dgGluingCompositionDiagonalKanObject (a := a) (d := d)).obj from
      dgGluingLastCompositionKanMap (a := a) g) :=
    compositionCorrespondenceDiagonal_fibration a g
  exact F2.spaceSquareCone_isLimit _ _ _ _ _

lemma dgGluingArrowCompositionCone_vertex :
    (dgGluingArrowCompositionCone f g).vertex =
      F2.coherentVertex (dgGluingArrowCompositionKanObject f g) :=
  F2.spaceSquareCone_vertex _ _ _ _ _

end SerrePositivity.InfinityCategories
