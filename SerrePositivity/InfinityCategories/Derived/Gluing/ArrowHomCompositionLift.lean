module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowHomCompositionFaces
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowCompositionPullback

/-! 矢印 Hom の元の二三角形を、同じ二つの合成対応へ持ち上げる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
variable {X T : SSet.{u}} {a b c d : X _⦋0⦌} (f : X.Edge a b) (g : X.Edge c d)
  (h : T ⟶ intervalMappingSpace (functorVertex (SSet.yonedaEquiv.symm f.edge))
    (functorVertex (SSet.yonedaEquiv.symm g.edge)))

def dgGluingArrowHomFirstComposition : T ⟶ dgGluingFirstFixedCompositionSpace f d :=
  dgGluingFirstFixedCompositionLift f d (dgGluingArrowHomTargetComponent f g h)
    (dgGluingArrowHomTrianglePairOfInterval _ _ h).first
    (dgGluingArrowHomTrianglePairOfInterval _ _ h).source
    (dgGluingArrowHomFirstTriangle_last f g h)

def dgGluingArrowHomLastComposition : T ⟶ compositionCorrespondence a g :=
  dgGluingLastFixedCompositionLift a g (dgGluingArrowHomSourceComponent f g h)
    (dgGluingArrowHomTrianglePairOfInterval _ _ h).second
    (dgGluingArrowHomSecondTriangle_first f g h)
    (dgGluingArrowHomTrianglePairOfInterval _ _ h).target

lemma dgGluingArrowHomComposition_diagonal :
    dgGluingArrowHomFirstComposition f g h ≫ dgGluingFirstFixedCompositionDiagonal f d =
      dgGluingArrowHomLastComposition f g h ≫ compositionCorrespondenceDiagonal a g := by
  apply intervalMappingUncurry_injective a d
  rw [dgGluingArrowHomFirstComposition, dgGluingFirstFixedCompositionLift_diagonal,
    dgGluingArrowHomLastComposition, dgGluingLastFixedCompositionLift_diagonal]
  exact (dgGluingArrowHomTrianglePairOfInterval _ _ h).diagonal

def dgGluingArrowHomToCompositionFamily : T ⟶ dgGluingArrowCompositionPullback f g :=
  pullback.lift (dgGluingArrowHomFirstComposition f g h) (dgGluingArrowHomLastComposition f g h)
    (dgGluingArrowHomComposition_diagonal f g h)

lemma dgGluingArrowHomToCompositionFamily_first :
    dgGluingArrowHomToCompositionFamily f g h ≫ pullback.fst _ _ =
      dgGluingArrowHomFirstComposition f g h :=
  pullback.lift_fst _ _ _

lemma dgGluingArrowHomToCompositionFamily_last :
    dgGluingArrowHomToCompositionFamily f g h ≫ pullback.snd _ _ =
      dgGluingArrowHomLastComposition f g h :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories
