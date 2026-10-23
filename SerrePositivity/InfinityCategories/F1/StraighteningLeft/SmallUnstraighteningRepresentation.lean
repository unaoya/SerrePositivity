module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Coherent.RepresentationExtension

/-!
概要：小さい unstraightening の元の図式による実際の相対表現。
方針：縮小前後の全空間の同型を、底上および各 fiber の同型として使う。
規約：底の quasicategory 性を要求しない。
使われ方：実際の straightening の余単位と本質的全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 小さい unstraightening は、縮小前の coherent な図式そのものの表現を持つ。 -/
def smallUnstraighteningTransportRepresentation {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    LeftTransportRepresentation
      ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection F)) where
  diagram := F
  comparison := (smallLeftUnstraighteningIso F).hom
  over_base := smallLeftUnstraighteningIso_projection F
  fiber_equivalence b := (qCatEquivalenceOfIso
    (vertexFiberIsoOfTotalIso _ _ (smallLeftUnstraighteningIso F)
      (smallLeftUnstraighteningIso_projection F) b)).isQCatEquivalence

/-- この相対表現は図式を選び直さず元の図式を厳密に保つ。 -/
lemma smallUnstraighteningTransportRepresentation_diagram {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    (smallUnstraighteningTransportRepresentation F).diagram = F := rfl

end SerrePositivity.InfinityCategories
