module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCommaHom
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientPathEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.KanPathPullbackTransport
public import SerrePositivity.InfinityCategories.Derived.PinchedComplexModelComparison
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q

/-- 係数複体は元の終域内の Hom そのものであり、同じ実 Hom 空間へ戻る。 -/
def dgGluingHomTargetCoefficientMappingIso :
    complexPinchedSpace.{u, max (u + 1) v} ((M).value X.left Y.right) ≅
      DGNerve.pinchedHom R E (p.obj X.left) (q.obj Y.right) :=
  (pinchedComplexModelIso (A := R) (p.obj X.left) (q.obj Y.right)).symm

/-- 左右の元入力を、元 augmentation による二作用として元 Hom 空間に置く。 -/
def dgGluingHomTargetCoefficientInputPair :=
  (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftAction R C D M X Y) ⊗ₘ
    complexPinchedMap.{u, max (u + 1) v} (dgGluingRightAction R C D M X Y)) ≫
      ((dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom ⊗ₘ
        (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom)

def dgGluingHomTargetCoefficientPathPullback : SSet.{max (u + 1) v} :=
  pullback (F2.arrowEndpointPair
    (DGNerve.pinchedHom R E (p.obj X.left) (q.obj Y.right)))
    (dgGluingHomTargetCoefficientInputPair R C D E p q X Y)

def dgGluingHomTargetCoefficientPathProjection :
    dgGluingHomTargetCoefficientPathPullback R C D E p q X Y ⟶
      (ihom (Δ[1] : SSet)).obj
        (DGNerve.pinchedHom R E (p.obj X.left) (q.obj Y.right)) :=
  pullback.fst _ _

def dgGluingHomTargetCoefficientInputProjection :
    dgGluingHomTargetCoefficientPathPullback R C D E p q X Y ⟶
      complexPinchedSpace.{u, max (u + 1) v} (homObject R C X.left Y.left) ⊗
        complexPinchedSpace.{u, max (u + 1) v} (homObject R D X.right Y.right) :=
  pullback.snd _ _

def dgGluingHomTargetCoefficientIntervalPath :
    complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y) ⟶
      (ihom (Δ[1] : SSet)).obj
        (DGNerve.pinchedHom R E (p.obj X.left) (q.obj Y.right)) :=
  dgGluingHomCoefficientIntervalPath R C D M X Y ≫
    (ihom (Δ[1] : SSet)).map
      (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom

def dgGluingHomTargetHomInputPair :
    complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y) ⟶
      complexPinchedSpace.{u, max (u + 1) v} (homObject R C X.left Y.left) ⊗
        complexPinchedSpace.{u, max (u + 1) v} (homObject R D X.right Y.right) :=
  lift (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y))
    (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y))

/-- 同じ二作用と第三 cochain の全 path を持つ、元終域内への実比較。 -/
def dgGluingHomTargetCoefficientPathComparison :
    complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y) ⟶
      dgGluingHomTargetCoefficientPathPullback R C D E p q X Y :=
  dgGluingHomCoefficientPathPullbackComparison R C D M X Y ≫
    dgGluingKanPathPullbackTransport
      (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom
      (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftAction R C D M X Y) ⊗ₘ
        complexPinchedMap.{u, max (u + 1) v} (dgGluingRightAction R C D M X Y))

attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetCoefficientPathComparison_path :
    dgGluingHomTargetCoefficientPathComparison R C D E p q X Y ≫
      dgGluingHomTargetCoefficientPathProjection R C D E p q X Y =
    dgGluingHomTargetCoefficientIntervalPath R C D E p q X Y := by
  let c := dgGluingHomCoefficientPathPullbackComparison R C D M X Y
  let e := (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom
  let a := complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftAction R C D M X Y) ⊗ₘ
    complexPinchedMap.{u, max (u + 1) v} (dgGluingRightAction R C D M X Y)
  have ht := congrArg (fun k => c ≫ k) (dgGluingKanPathPullbackTransport_path e a)
  have hc := congrArg (fun k => k ≫ (ihom (Δ[1] : SSet)).map e)
    (dgGluingHomCoefficientPathPullbackComparison_path R C D M X Y)
  exact (Category.assoc c (dgGluingKanPathPullbackTransport e a)
    (dgGluingHomTargetCoefficientPathProjection R C D E p q X Y)).trans
      (ht.trans ((Category.assoc c (pullback.fst _ _) ((ihom (Δ[1] : SSet)).map e)).symm.trans hc))

lemma dgGluingHomTargetCoefficientPathComparison_inputs :
    dgGluingHomTargetCoefficientPathComparison R C D E p q X Y ≫
      dgGluingHomTargetCoefficientInputProjection R C D E p q X Y =
    dgGluingHomTargetHomInputPair R C D E p q X Y := by
  let c := dgGluingHomCoefficientPathPullbackComparison R C D M X Y
  let e := (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom
  let a := complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftAction R C D M X Y) ⊗ₘ
    complexPinchedMap.{u, max (u + 1) v} (dgGluingRightAction R C D M X Y)
  have ht := congrArg (fun k => c ≫ k) (dgGluingKanPathPullbackTransport_inputs e a)
  exact (Category.assoc c (dgGluingKanPathPullbackTransport e a)
    (dgGluingHomTargetCoefficientInputProjection R C D E p q X Y)).trans
      (ht.trans (dgGluingHomCoefficientPathPullbackComparison_inputs R C D M X Y))

lemma dgGluingHomTargetCoefficientPathComparison_equivalence :
    IsSimplicialHomotopyEquivalence
      (dgGluingHomTargetCoefficientPathComparison R C D E p q X Y) := by
  let := F2.kanComplex_tensor
    (complexPinchedSpace.{u, max (u + 1) v} (homObject R C X.left Y.left))
    (complexPinchedSpace.{u, max (u + 1) v} (homObject R D X.right Y.right))
  let : KanComplex (dgGluingHomCoefficientPathPullback R C D M X Y) :=
    dgGluingKanPathPullback_kanComplex _
  let : KanComplex (dgGluingHomTargetCoefficientPathPullback R C D E p q X Y) :=
    dgGluingKanPathPullback_kanComplex _
  exact (dgGluingHomCoefficientPathPullbackComparison_equivalence R C D M X Y).comp
    (dgGluingKanPathPullbackTransport_equivalence _ _
      (HomotopyLimits.homotopyEquivalence_of_isIso
        (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom))

end SerrePositivity.InfinityCategories
