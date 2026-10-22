module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowCompositionIso
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowCompositionLimit

/-! 元の矢印 Hom 自体を頂点とし、同じ対角二射の空間の ∞ 極限錐を供給する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
variable {X : SSet.{u}} {a b c d : X _⦋0⦌} (f : X.Edge a b) (g : X.Edge c d)

lemma dgGluingArrowHomComposition_isPullback :
    IsPullback
      ((dgGluingArrowCompositionIso f g).inv ≫ pullback.snd _ _)
      ((dgGluingArrowCompositionIso f g).inv ≫ pullback.fst _ _)
      (compositionCorrespondenceDiagonal a g) (dgGluingFirstFixedCompositionDiagonal f d) := by
  refine (IsPullback.of_hasPullback (dgGluingFirstFixedCompositionDiagonal f d)
    (compositionCorrespondenceDiagonal a g)).flip.of_iso
      (dgGluingArrowCompositionIso f g) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  all_goals simp

variable [Quasicategory X]

def dgGluingArrowHomCompositionKanObject : KanObject.{u} :=
  ⟨intervalMappingSpace (functorVertex (SSet.yonedaEquiv.symm f.edge))
    (functorVertex (SSet.yonedaEquiv.symm g.edge)), inferInstance⟩

def dgGluingArrowHomCompositionCone :
    JoinCone (kanDiagramCoherentNerve (dgGluingArrowCompositionDiagram f g)) :=
  F2.spaceSquareCone (K := dgGluingArrowHomCompositionKanObject f g)
    (dgGluingLastCompositionKanMap (a := a) g) (dgGluingFirstCompositionKanMap (d := d) f)
    ((dgGluingArrowCompositionIso f g).inv ≫ pullback.snd _ _)
    ((dgGluingArrowCompositionIso f g).inv ≫ pullback.fst _ _)
    (dgGluingArrowHomComposition_isPullback f g)

lemma dgGluingArrowHomCompositionCone_isLimit :
    IsLimitCone (dgGluingArrowHomCompositionCone f g) := by
  let : Fibration (show (dgGluingLastCompositionKanObject (a := a) g).obj ⟶
      (dgGluingCompositionDiagonalKanObject (a := a) (d := d)).obj from
      dgGluingLastCompositionKanMap (a := a) g) :=
    compositionCorrespondenceDiagonal_fibration a g
  exact F2.spaceSquareCone_isLimit _ _ _ _ _

lemma dgGluingArrowHomCompositionCone_vertex :
    (dgGluingArrowHomCompositionCone f g).vertex =
      F2.coherentVertex (dgGluingArrowHomCompositionKanObject f g) :=
  F2.spaceSquareCone_vertex _ _ _ _ _

end SerrePositivity.InfinityCategories
