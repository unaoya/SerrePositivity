module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomTargetCommaHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.HomCoefficientPathEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.KanPathPullbackTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedComplexModelComparison
/-!
概要：元二脚の Hom 複体を、元終域の実 Hom 空間内の path 引き戻しへ比較する。
方針：同じ mapping cocone の係数 path を元終域の Hom 模型同型で輸送する。
規約：元の左右 Hom 入力を厳密に保持し、導来加群値を経由しない。
使われ方：元終域向け lax Hom 比較の、実係数 path 側の同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q

/-- 係数複体は元の終域内の Hom そのものであり、同じ実 Hom 空間へ戻る。 -/
def dgGluingHomTargetCoefficientMappingIso :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} ((M).value X.left Y.right) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E (p.obj X.left) (q.obj Y.right) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (A := R) (p.obj X.left) (q.obj Y.right)).symm

/-- 左右の元入力を、元 augmentation による二作用として元 Hom 空間に置く。 -/
def dgGluingHomTargetCoefficientInputPair :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) ⊗ₘ
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y)) ≫
      ((dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom ⊗ₘ
        (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom)

def dgGluingHomTargetCoefficientPathPullback : SSet.{max (u + 1) v} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E (p.obj X.left) (q.obj Y.right)))
    (dgGluingHomTargetCoefficientInputPair R C D E p q X Y)

def dgGluingHomTargetCoefficientPathProjection :
    dgGluingHomTargetCoefficientPathPullback R C D E p q X Y ⟶
      (ihom (Δ[1] : SSet)).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E (p.obj X.left) (q.obj Y.right)) :=
  pullback.fst _ _

def dgGluingHomTargetCoefficientInputProjection :
    dgGluingHomTargetCoefficientPathPullback R C D E p q X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (homObject R C X.left Y.left) ⊗
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (homObject R D X.right Y.right) :=
  pullback.snd _ _

def dgGluingHomTargetCoefficientIntervalPath :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y) ⟶
      (ihom (Δ[1] : SSet)).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E (p.obj X.left) (q.obj Y.right)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientIntervalPath R C D M X Y ≫
    (ihom (Δ[1] : SSet)).map
      (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom

def dgGluingHomTargetHomInputPair :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (homObject R C X.left Y.left) ⊗
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (homObject R D X.right Y.right) :=
  lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y))

/-- 同じ二作用と第三 cochain の全 path を持つ、元終域内への実比較。 -/
def dgGluingHomTargetCoefficientPathComparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y) ⟶
      dgGluingHomTargetCoefficientPathPullback R C D E p q X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientPathPullbackComparison R C D M X Y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullbackTransport
      (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y))

attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetCoefficientPathComparison_path :
    dgGluingHomTargetCoefficientPathComparison R C D E p q X Y ≫
      dgGluingHomTargetCoefficientPathProjection R C D E p q X Y =
    dgGluingHomTargetCoefficientIntervalPath R C D E p q X Y := by
  let c := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientPathPullbackComparison R C D M X Y
  let e := (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom
  let a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) ⊗ₘ
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y)
  have ht := congrArg (fun k => c ≫ k) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullbackTransport_path e a)
  have hc := congrArg (fun k => k ≫ (ihom (Δ[1] : SSet)).map e)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientPathPullbackComparison_path R C D M X Y)
  exact (Category.assoc c (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullbackTransport e a)
    (dgGluingHomTargetCoefficientPathProjection R C D E p q X Y)).trans
      (ht.trans ((Category.assoc c (pullback.fst _ _) ((ihom (Δ[1] : SSet)).map e)).symm.trans hc))

lemma dgGluingHomTargetCoefficientPathComparison_inputs :
    dgGluingHomTargetCoefficientPathComparison R C D E p q X Y ≫
      dgGluingHomTargetCoefficientInputProjection R C D E p q X Y =
    dgGluingHomTargetHomInputPair R C D E p q X Y := by
  let c := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientPathPullbackComparison R C D M X Y
  let e := (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom
  let a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) ⊗ₘ
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y)
  have ht := congrArg (fun k => c ≫ k) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullbackTransport_inputs e a)
  exact (Category.assoc c (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullbackTransport e a)
    (dgGluingHomTargetCoefficientInputProjection R C D E p q X Y)).trans
      (ht.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientPathPullbackComparison_inputs R C D M X Y))

lemma dgGluingHomTargetCoefficientPathComparison_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (dgGluingHomTargetCoefficientPathComparison R C D E p q X Y) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanComplex_tensor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (homObject R C X.left Y.left))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (homObject R D X.right Y.right))
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientPathPullback R C D M X Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullback_kanComplex _
  let : KanComplex (dgGluingHomTargetCoefficientPathPullback R C D E p q X Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullback_kanComplex _
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientPathPullbackComparison_equivalence R C D M X Y).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKanPathPullbackTransport_equivalence _ _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.homotopyEquivalence_of_isIso
        (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
