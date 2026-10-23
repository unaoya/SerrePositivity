module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityEvaluationFiberPre
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeFiberColimitCriterion
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.PrecompositionTargetComparison

/-!
概要：元の F を頂点とする同じ密度余錐の各評価は、元の評価図式の余極限。
方針：実際の fiber 値写像の前合成同値を pointed fiber 標的へ戻し、native な余錐判定を使う。
規約：同じ余錐と指定頂点を保ち、余極限候補を選び直さない。
使われ方：HTT 5.1.5.3 の元の小さい表現可能図式による密度。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)

/-- 同じ評価余錐の実際の fiber 写像は、必要な全 pointed fiber 標的への前合成同値。 -/
lemma presheafDensityEvaluationCoconeFiberMap_pre (w : SpaceInfinity.{u} _⦋0⦌) :
    IsSimplicialHomotopyEquivalence
      ((pre (F2.coconeFiberMap (presheafDensityEvaluationCocone F x))).app
        (vertexFiber pointedSpaceProjection w)) := by
  let c := presheafDensityEvaluationCocone F x
  let v := presheafDensityEvaluationVertex F x
  let h : c.vertex = v := presheafDensityEvaluationCocone_vertex F x
  let Z := (SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject w).obj
  have hd := presheafDensityEvaluationCoconeFiberValueMap_pre F x (spaceInfinityObject w).obj
  let r : vertexFiber pointedSpaceProjection c.vertex ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject v).obj :=
    eqToHom (congrArg (vertexFiber pointedSpaceProjection) h) ≫
      (pointedSpaceFiberValueEquivalence v).hom
  have heq := (qCatEquivalenceOfIso
    (eqToIso (congrArg (vertexFiber pointedSpaceProjection) h))).isQCatEquivalence
  have hr : IsQCatEquivalence r :=
    heq.comp (pointedSpaceFiberValueEquivalence v).isQCatEquivalence
  have hp : IsSimplicialHomotopyEquivalence ((pre (F2.coconeFiberMap c)).app Z) := by
    have hrp := (hr.precompose Z).isSimplicialHomotopyEquivalence
    change IsSimplicialHomotopyEquivalence ((pre (F2.coconeFiberMap c ≫ r)).app Z) at hd
    rw [pre_map, NatTrans.comp_app] at hd
    exact hrp.cancel_left hd
  exact F2.pre_homotopyEquivalence_of_target_equivalence (F2.coconeFiberMap c)
    (pointedSpaceFiberValueEquivalence w).hom
    (pointedSpaceFiberValueEquivalence w).isQCatEquivalence hp

/-- 元の同じ密度余錐の各評価は、元の小さい評価図式の余極限。 -/
lemma presheafDensityEvaluationCocone_isColimit :
    IsColimitCone (presheafDensityEvaluationCocone F x) :=
  F2.isColimitCone_of_coconeFiberMap_pre_homotopyEquivalence _
    (presheafDensityEvaluationCoconeFiberMap_pre F x)

end SerrePositivity.InfinityCategories.F2.Ind
