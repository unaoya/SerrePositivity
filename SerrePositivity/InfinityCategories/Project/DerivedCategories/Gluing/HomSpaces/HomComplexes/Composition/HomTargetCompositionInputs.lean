module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomTargetCompositionTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.FirstFixedCompositionLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.LastFixedCompositionLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.TrivialKanSectionEquivalence
/-!
概要：元二脚の左右入力を保持する二つの合成対応と実入力 fiber を構成する。
方針：元終域の標準三角形を持ち上げ、元 Hom 入力に沿って引き戻す。
規約：実射・全三角形・元入力を回収する。使われ方：元 lax Hom の相対比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetFirstComposition :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionLift.{max (u + 1) v} (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
    (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (q.obj Y.right))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightIntervalInput R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightCompositionTriangle R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightCompositionTriangle_fixed R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightCompositionTriangle_variable R C D E p q X Y)

def dgGluingHomTargetLastComposition :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastFixedCompositionLift.{max (u + 1) v} (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (p.obj X.left))
    (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftIntervalInput R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftCompositionTriangle R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftCompositionTriangle_variable R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftCompositionTriangle_fixed R C D E p q X Y)

def dgGluingHomTargetFirstInputFiber :=
  pullback
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond.{max (u + 1) v} (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
      (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (q.obj Y.right)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightIntervalInput R C D E p q X Y)

def dgGluingHomTargetLastInputFiber :=
  pullback
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst.{max (u + 1) v} (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (p.obj X.left))
      (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftIntervalInput R C D E p q X Y)

def dgGluingHomTargetFirstInputProjection :=
  pullback.snd
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond.{max (u + 1) v} (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
      (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (q.obj Y.right)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightIntervalInput R C D E p q X Y)

def dgGluingHomTargetLastInputProjection :=
  pullback.snd
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst.{max (u + 1) v} (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (p.obj X.left))
      (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftIntervalInput R C D E p q X Y)

lemma dgGluingHomTargetFirstInputProjection_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (dgGluingHomTargetFirstInputProjection R C D E p q X Y) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond.{max (u + 1) v} (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
      (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (q.obj Y.right))) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond_trivialKanFibration _ _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

lemma dgGluingHomTargetLastInputProjection_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (dgGluingHomTargetLastInputProjection R C D E p q X Y) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst.{max (u + 1) v} (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (p.obj X.left))
      (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y)))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst_trivialKanFibration _ _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

def dgGluingHomTargetFirstInputSection :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (homObject R D X.right Y.right) ⟶
      dgGluingHomTargetFirstInputFiber R C D E p q X Y :=
  pullback.lift (dgGluingHomTargetFirstComposition R C D E p q X Y) (𝟙 _)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionLift_second _ _ _ _ _ _).trans
      (Category.id_comp _).symm)

def dgGluingHomTargetLastInputSection :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (homObject R C X.left Y.left) ⟶
      dgGluingHomTargetLastInputFiber R C D E p q X Y :=
  pullback.lift (dgGluingHomTargetLastComposition R C D E p q X Y) (𝟙 _)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastFixedCompositionLift_first _ _ _ _ _ _).trans
      (Category.id_comp _).symm)

lemma dgGluingHomTargetFirstInputSection_input :
    dgGluingHomTargetFirstInputSection R C D E p q X Y ≫
      dgGluingHomTargetFirstInputProjection R C D E p q X Y = 𝟙 _ :=
  pullback.lift_snd _ _ _

lemma dgGluingHomTargetLastInputSection_input :
    dgGluingHomTargetLastInputSection R C D E p q X Y ≫
      dgGluingHomTargetLastInputProjection R C D E p q X Y = 𝟙 _ :=
  pullback.lift_snd _ _ _

lemma dgGluingHomTargetFirstInputSection_composition :
    dgGluingHomTargetFirstInputSection R C D E p q X Y ≫
      pullback.fst
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
          (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (q.obj Y.right)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightIntervalInput R C D E p q X Y) =
      dgGluingHomTargetFirstComposition R C D E p q X Y :=
  pullback.lift_fst _ _ _

lemma dgGluingHomTargetLastInputSection_composition :
    dgGluingHomTargetLastInputSection R C D E p q X Y ≫
      pullback.fst
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (p.obj X.left))
          (Edge.ofTruncated (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y))))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftIntervalInput R C D E p q X Y) =
      dgGluingHomTargetLastComposition R C D E p q X Y :=
  pullback.lift_fst _ _ _

lemma dgGluingHomTargetFirstInputSection_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgGluingHomTargetFirstInputSection R C D E p q X Y) := by
  let := dgGluingHomTargetFirstInputProjection_trivialKanFibration R C D E p q X Y
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTrivialKanSection_equivalence
    (dgGluingHomTargetFirstInputProjection R C D E p q X Y)
    (dgGluingHomTargetFirstInputSection R C D E p q X Y)
    (dgGluingHomTargetFirstInputSection_input R C D E p q X Y)

lemma dgGluingHomTargetLastInputSection_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgGluingHomTargetLastInputSection R C D E p q X Y) := by
  let := dgGluingHomTargetLastInputProjection_trivialKanFibration R C D E p q X Y
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTrivialKanSection_equivalence
    (dgGluingHomTargetLastInputProjection R C D E p q X Y)
    (dgGluingHomTargetLastInputSection R C D E p q X Y)
    (dgGluingHomTargetLastInputSection_input R C D E p q X Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
