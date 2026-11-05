module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxArrowTransport
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxHomComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedIntervalPullbackTransport
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetArrowComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomMappingModel
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIsoPrecomposition
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackMapping
public import SerrePositivity.InfinityCategories.Core.FullyFaithful
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "F" => dgGluingHomTargetNerveLaxComparison R C D E p q
variable (X : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

def dgGluingHomTargetLaxHomArrowVertex :=
  (F2.laxPullbackArrow (dgNerve.map p) (dgNerve.map q)).app (Opposite.op ⦋0⦌)
    ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex X))

lemma dgGluingHomTargetLaxHomArrowVertex_diagram :
    dgGluingHomTargetLaxHomArrowVertex R C D E p q X =
    functorVertex (dgGluingHomTargetArrowDiagram R C D E p q X) := by
  have hc := congrArg (fun k => k.app (Opposite.op ⦋0⦌) (Simplex.vertex (A := R) X))
    (dgGluingHomTargetNerveLaxComparison_arrow R C D E p q)
  exact hc.trans (dgGluingHomTargetArrowDiagram_vertex R C D E p q X)

variable (Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

def dgGluingHomTargetLaxHomPinchedInputBase :=
  pinchedHomPullbackBaseMap (F2.arrowEndpointPair (dgNerve R E))
    (dgNerve.map p ⊗ₘ dgNerve.map q)
    ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex X))
    ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex Y))

def dgGluingHomTargetLaxHomIntervalEndpointMap :=
  intervalMappingPostOfEq (F2.arrowEndpointPair (dgNerve R E))
    (dgGluingHomTargetLaxHomArrowVertex R C D E p q X)
    (dgGluingHomTargetLaxHomArrowVertex R C D E p q Y) rfl rfl

def dgGluingHomTargetLaxHomIntervalInputBase :=
  dgGluingHomTargetLaxHomPinchedInputBase R C D E p q X Y ≫
    pinchedHomToIntervalMappingSpace _ _

def dgGluingHomTargetLaxHomIntervalPullback : SSet.{max (u + 1) v} := by
  letI : Limits.HasLimit (cospan
      (dgGluingHomTargetLaxHomIntervalEndpointMap R C D E p q X Y)
      (dgGluingHomTargetLaxHomIntervalInputBase R C D E p q X Y)) :=
    HasLimitsOfShape.has_limit _
  exact pullback (dgGluingHomTargetLaxHomIntervalEndpointMap R C D E p q X Y)
    (dgGluingHomTargetLaxHomIntervalInputBase R C D E p q X Y)

def dgGluingHomTargetLaxHomPinchedIntervalTransport :
    dgGluingHomTargetLaxHomPullback R C D E p q X Y ⟶
      dgGluingHomTargetLaxHomIntervalPullback R C D E p q X Y :=
  dgGluingPinchedIntervalPullbackTransport (F2.arrowEndpointPair (dgNerve R E))
    (dgGluingHomTargetLaxHomArrowVertex R C D E p q X)
    (dgGluingHomTargetLaxHomArrowVertex R C D E p q Y)
    (dgGluingHomTargetLaxHomPinchedInputBase R C D E p q X Y)

lemma dgGluingHomTargetLaxHomPinchedIntervalTransport_equivalence :
    IsSimplicialHomotopyEquivalence
      (dgGluingHomTargetLaxHomPinchedIntervalTransport R C D E p q X Y) := by
  letI := F2.quasicategory_tensor (dgNerve R E) (dgNerve R E)
  letI := F2.quasicategory_tensor (dgNerve R C) (dgNerve R D)
  exact dgGluingPinchedIntervalPullbackTransport_equivalence
    (F2.arrowEndpointPair (dgNerve R E))
    (dgGluingHomTargetLaxHomArrowVertex R C D E p q X)
    (dgGluingHomTargetLaxHomArrowVertex R C D E p q Y)
    (dgGluingHomTargetLaxHomPinchedInputBase R C D E p q X Y)
    (F2.arrowEndpointPair_kanEquivalenceLifting (dgNerve R E))

lemma dgGluingHomTargetLaxHomPullback_kanComplex :
    KanComplex (dgGluingHomTargetLaxHomPullback R C D E p q X Y) := by
  letI := F2.quasicategory_tensor (dgNerve R E) (dgNerve R E)
  letI := F2.quasicategory_tensor (dgNerve R C) (dgNerve R D)
  change KanComplex (pullback
    (pinchedHomMap (F2.arrowEndpointPair (dgNerve R E))
      (dgGluingHomTargetLaxHomArrowVertex R C D E p q X)
      (dgGluingHomTargetLaxHomArrowVertex R C D E p q Y))
    (dgGluingHomTargetLaxHomPinchedInputBase R C D E p q X Y))
  exact HomotopyLimits.pullback_kanComplex_of_fibration _ _

def dgGluingHomTargetLaxHomInputVertex
    (Z : DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) :=
  (pullback.snd (F2.arrowEndpointPair (dgNerve R E))
    (dgNerve.map p ⊗ₘ dgNerve.map q)).app (Opposite.op ⦋0⦌)
      ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex Z))

def dgGluingHomTargetLaxHomIntervalArrowProjection :
    dgGluingHomTargetLaxHomIntervalPullback R C D E p q X Y ⟶
      intervalMappingSpace (dgGluingHomTargetLaxHomArrowVertex R C D E p q X)
        (dgGluingHomTargetLaxHomArrowVertex R C D E p q Y) := pullback.fst _ _

def dgGluingHomTargetLaxHomIntervalInputProjection :
    dgGluingHomTargetLaxHomIntervalPullback R C D E p q X Y ⟶
      InfinityCategories.pinchedHom (dgGluingHomTargetLaxHomInputVertex R C D E p q X)
        (dgGluingHomTargetLaxHomInputVertex R C D E p q Y) := pullback.snd _ _

def dgGluingHomTargetLaxHomInputProjection :
    dgGluingHomTargetLaxHomPullback R C D E p q X Y ⟶
      InfinityCategories.pinchedHom (dgGluingHomTargetLaxHomInputVertex R C D E p q X)
        (dgGluingHomTargetLaxHomInputVertex R C D E p q Y) := pullback.snd _ _

lemma dgGluingHomTargetLaxHomPinchedIntervalTransport_arrow :
    dgGluingHomTargetLaxHomPinchedIntervalTransport R C D E p q X Y ≫
      dgGluingHomTargetLaxHomIntervalArrowProjection R C D E p q X Y =
    dgGluingHomTargetLaxHomArrowProjection R C D E p q X Y ≫
      pinchedHomToIntervalMappingSpace _ _ := pullback.lift_fst _ _ _

lemma dgGluingHomTargetLaxHomPinchedIntervalTransport_inputs :
    dgGluingHomTargetLaxHomPinchedIntervalTransport R C D E p q X Y ≫
      dgGluingHomTargetLaxHomIntervalInputProjection R C D E p q X Y =
    dgGluingHomTargetLaxHomInputProjection R C D E p q X Y :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

end SerrePositivity.InfinityCategories
