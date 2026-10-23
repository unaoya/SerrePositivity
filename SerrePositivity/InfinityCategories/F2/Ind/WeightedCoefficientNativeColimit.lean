module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeFiberPre
public import SerrePositivity.InfinityCategories.F2.Ind.KappaColimits
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeFiberColimitCriterion
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.PrecompositionTargetComparison

/-!
概要：元の全 weighted 密度変換の同じ係数制限を実現した指定 native 余錐は余極限。
方針：同じ実際の評価 fiber 値写像の前合成同値を native 判定へ戻し、評価と包含で検出。
規約：元の余錐・全円柱・指定頂点を固定。使われ方：元の全変換の局所 Kan 普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I) (x : C _⦋0⦌)

/-- 元の native 評価余錐の実際の fiber 写像は、全ての必要な pointed fiber 標的で前合成同値。 -/
lemma weightedCoefficientNativeCoconeFiberMap_pre (w : SpaceInfinity.{u} _⦋0⦌) :
    IsSimplicialHomotopyEquivalence
      ((pre (F2.coconeFiberMap (weightedCoefficientNativeEvaluationCocone κ F hF i x))).app
        (vertexFiber pointedSpaceProjection w)) := by
  let c := weightedCoefficientNativeEvaluationCocone κ F hF i x
  let v := weightedCoefficientNativeEvaluationVertex κ F hF i x
  let h : c.vertex = v := weightedCoefficientNativeEvaluationCocone_vertex κ F hF i x
  let Z := (SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject w).obj
  have hd := weightedCoefficientNativeCoconeFiberValueMap_pre κ F hF i x (spaceInfinityObject w).obj
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

/-- 元の同じ native 係数余錐の各評価は、同じ評価図式の余極限。 -/
lemma weightedCoefficientNativeEvaluationCocone_isColimit :
    IsColimitCone (weightedCoefficientNativeEvaluationCocone κ F hF i x) :=
  F2.isColimitCone_of_coconeFiberMap_pre_homotopyEquivalence _
    (weightedCoefficientNativeCoconeFiberMap_pre κ F hF i x)

omit x in
/-- 同じ全 weighted 密度変換の係数制限を実現した、元の指定 native 係数余錐は余極限。 -/
lemma weightedIndDensityCoefficientCocone_isColimit :
    IsColimitCone (weightedIndDensityCoefficientCocone κ F hF i) := by
  apply ind_isColimit_of_inclusion κ (weightedIndCoefficientDiagram κ F i)
  apply presheafInfinity_isColimit_of_evaluation
    (weightedIndCoefficientDiagram κ F i ≫ indInclusionPresheaf κ C)
  intro x
  exact weightedCoefficientNativeEvaluationCocone_isColimit κ F hF i x

end SerrePositivity.InfinityCategories.F2.Ind
