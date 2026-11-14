module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.DerivedCompositionInputFibers

/-! 元の二三角形による入力 fiber の実切断は、射影と全三角形を保持する同値。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedFirstCompositionInputSection (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (homObject R D X.right Y.right)) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputFiber R C D M X Y :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstComposition R C D M X Y) (𝟙 _) (by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstComposition_input R C D M X Y, Category.id_comp])

def dgGluingDerivedLastCompositionInputSection (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (homObject R C X.left Y.left)) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputFiber R C D M X Y :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastComposition R C D M X Y) (𝟙 _) (by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastComposition_input R C D M X Y, Category.id_comp])

lemma dgGluingDerivedFirstCompositionInputSection_input (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingDerivedFirstCompositionInputSection R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputProjection R C D M X Y = 𝟙 _ :=
  pullback.lift_snd _ _ _

lemma dgGluingDerivedLastCompositionInputSection_input (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingDerivedLastCompositionInputSection R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputProjection R C D M X Y = 𝟙 _ :=
  pullback.lift_snd _ _ _

lemma dgGluingDerivedFirstCompositionInputSection_composition (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingDerivedFirstCompositionInputSection R C D M X Y ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstComposition R C D M X Y :=
  pullback.lift_fst _ _ _

lemma dgGluingDerivedLastCompositionInputSection_composition (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingDerivedLastCompositionInputSection R C D M X Y ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastComposition R C D M X Y :=
  pullback.lift_fst _ _ _

lemma dgGluingDerivedFirstCompositionInputSection_equivalence (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgGluingDerivedFirstCompositionInputSection R C D M X Y) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputProjection_trivialKanFibration R C D M X Y
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTrivialKanSection_equivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputProjection R C D M X Y)
    (dgGluingDerivedFirstCompositionInputSection R C D M X Y)
    (dgGluingDerivedFirstCompositionInputSection_input R C D M X Y)

lemma dgGluingDerivedLastCompositionInputSection_equivalence (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgGluingDerivedLastCompositionInputSection R C D M X Y) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputProjection_trivialKanFibration R C D M X Y
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTrivialKanSection_equivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputProjection R C D M X Y)
    (dgGluingDerivedLastCompositionInputSection R C D M X Y)
    (dgGluingDerivedLastCompositionInputSection_input R C D M X Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
