module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.HomTargetLaxArrowTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.HomTargetLaxHomComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.PinchedIntervalPullbackTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.HomTargetArrowComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomMappingModel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Actions.HomotopyIsoPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackMapping
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
/-!
概要：元 Hom gluing の同じ Hom 複体から、元二脚の lax 写像空間への実比較。
方針：元 nerve の Hom 模型同型と F2 の実 Hom pullback 表示を合成する。
規約：元比較の実作用を保ち、同値性を新しい主経路の仮定にはしない。
使われ方：元終域の全 Hom 比較を左右入力・比較辺全族のまま検証する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed DifferentialGraded SSet
open KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNerveLaxComparison R C D E p q
variable (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

def dgGluingHomTargetLaxHomArrowVertex :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map q)).app (Opposite.op ⦋0⦌)
    ((F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))

lemma dgGluingHomTargetLaxHomArrowVertex_diagram :
    dgGluingHomTargetLaxHomArrowVertex R C D E p q X =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowDiagram R C D E p q X) := by
  have hc := congrArg (fun k => k.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) X))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNerveLaxComparison_arrow R C D E p q)
  exact hc.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowDiagram_vertex R C D E p q X)

variable (Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

def dgGluingHomTargetLaxHomPinchedInputBase :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackBaseMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map p ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map q)
    ((F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))
    ((F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y))

def dgGluingHomTargetLaxHomIntervalEndpointMap :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E))
    (dgGluingHomTargetLaxHomArrowVertex R C D E p q X)
    (dgGluingHomTargetLaxHomArrowVertex R C D E p q Y) rfl rfl

def dgGluingHomTargetLaxHomIntervalInputBase :=
  dgGluingHomTargetLaxHomPinchedInputBase R C D E p q X Y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _

def dgGluingHomTargetLaxHomIntervalPullback : SSet.{max (u + 1) v} := by
  letI : Limits.HasLimit (cospan
      (dgGluingHomTargetLaxHomIntervalEndpointMap R C D E p q X Y)
      (dgGluingHomTargetLaxHomIntervalInputBase R C D E p q X Y)) :=
    HasLimitsOfShape.has_limit _
  exact pullback (dgGluingHomTargetLaxHomIntervalEndpointMap R C D E p q X Y)
    (dgGluingHomTargetLaxHomIntervalInputBase R C D E p q X Y)

def dgGluingHomTargetLaxHomPinchedIntervalTransport :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPullback R C D E p q X Y ⟶
      dgGluingHomTargetLaxHomIntervalPullback R C D E p q X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedIntervalPullbackTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E))
    (dgGluingHomTargetLaxHomArrowVertex R C D E p q X)
    (dgGluingHomTargetLaxHomArrowVertex R C D E p q Y)
    (dgGluingHomTargetLaxHomPinchedInputBase R C D E p q X Y)

lemma dgGluingHomTargetLaxHomPinchedIntervalTransport_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (dgGluingHomTargetLaxHomPinchedIntervalTransport R C D E p q X Y) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategory_tensor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategory_tensor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedIntervalPullbackTransport_equivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E))
    (dgGluingHomTargetLaxHomArrowVertex R C D E p q X)
    (dgGluingHomTargetLaxHomArrowVertex R C D E p q Y)
    (dgGluingHomTargetLaxHomPinchedInputBase R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair_kanEquivalenceLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E))

lemma dgGluingHomTargetLaxHomPullback_kanComplex :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPullback R C D E p q X Y) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategory_tensor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategory_tensor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)
  change KanComplex (pullback
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E))
      (dgGluingHomTargetLaxHomArrowVertex R C D E p q X)
      (dgGluingHomTargetLaxHomArrowVertex R C D E p q Y))
    (dgGluingHomTargetLaxHomPinchedInputBase R C D E p q X Y))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pullback_kanComplex_of_fibration _ _

def dgGluingHomTargetLaxHomInputVertex
    (Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) :=
  (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map p ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map q)).app (Opposite.op ⦋0⦌)
      ((F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Z))

def dgGluingHomTargetLaxHomIntervalArrowProjection :
    dgGluingHomTargetLaxHomIntervalPullback R C D E p q X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (dgGluingHomTargetLaxHomArrowVertex R C D E p q X)
        (dgGluingHomTargetLaxHomArrowVertex R C D E p q Y) := pullback.fst _ _

def dgGluingHomTargetLaxHomIntervalInputProjection :
    dgGluingHomTargetLaxHomIntervalPullback R C D E p q X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (dgGluingHomTargetLaxHomInputVertex R C D E p q X)
        (dgGluingHomTargetLaxHomInputVertex R C D E p q Y) := pullback.snd _ _

def dgGluingHomTargetLaxHomInputProjection :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPullback R C D E p q X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (dgGluingHomTargetLaxHomInputVertex R C D E p q X)
        (dgGluingHomTargetLaxHomInputVertex R C D E p q Y) := pullback.snd _ _

lemma dgGluingHomTargetLaxHomPinchedIntervalTransport_arrow :
    dgGluingHomTargetLaxHomPinchedIntervalTransport R C D E p q X Y ≫
      dgGluingHomTargetLaxHomIntervalArrowProjection R C D E p q X Y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomArrowProjection R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _ := pullback.lift_fst _ _ _

lemma dgGluingHomTargetLaxHomPinchedIntervalTransport_inputs :
    dgGluingHomTargetLaxHomPinchedIntervalTransport R C D E p q X Y ≫
      dgGluingHomTargetLaxHomIntervalInputProjection R C D E p q X Y =
    dgGluingHomTargetLaxHomInputProjection R C D E p q X Y :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
