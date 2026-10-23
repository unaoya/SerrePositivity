module

public import SerrePositivity.InfinityCategories.F1.Simplicial.SimplicialOverTestBifunctor
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorActionEvaluation
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedComparisonIso
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverEquivalence
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationCoherentEvaluation

/-!
概要：底上の豊穣比較から、二変数の相対 Hom テストの共同関手同型を構成する。
方針：比較の全 Hom の自然性を前合成と後合成の同時評価へ適用し、全対象で共同実現する。
規約：固定始域ごとの同型を独立に選ばず、一つの豊穣比較から同じ族を得る。
使われ方：自然な復元 span の逆を二変数で同時に実現する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 底上の豊穣比較は、始域とテスト標的の双方に自然な前合成の豊穣比較を与える。 -/
def SimplicialOverComparison.jointTestComparison {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}}
    {F G : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)}
    (η : SimplicialOverComparison F G) :
    KanEnrichedComparison (simplicialOverTestBifunctor G) (simplicialOverTestBifunctor F) := by
  refine ⟨fun X ↦ relativeFunctorOverPre X.2.val.hom (η.val X.1.unop), ?_⟩
  intro X Y
  change (relativeFunctorOverPre X.2.val.hom (η.val X.1.unop) ▷
      SimplicialCategory.sHom X Y) ≫
      uncurry ((simplicialOverTestSource F).map X Y ≫
        curry (simplicialOverTestAction ((simplicialOverTestSource F).obj X)
          ((simplicialOverTestSource F).obj Y))) =
    uncurry ((simplicialOverTestSource G).map X Y ≫
      curry (simplicialOverTestAction ((simplicialOverTestSource G).obj X)
        ((simplicialOverTestSource G).obj Y))) ≫
      relativeFunctorOverPre Y.2.val.hom (η.val Y.1.unop)
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_curry, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨f, ⟨a, b⟩⟩
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  have h := congrArg (fun t : SimplicialCategory.sHom Y.1.unop X.1.unop ⟶
      relativeFunctorSpace (G.obj X.1.unop).val.hom (F.obj Y.1.unop).val.hom ↦
        ((t.app n a).val.app d α) x) (η.property Y.1.unop X.1.unop)
  change (((HomotopyLimits.relativeFunctorPost (F.obj X.1.unop).val.hom
    (G.obj X.1.unop).val.hom (η.val X.1.unop).left (η.val X.1.unop).w
    (F.obj Y.1.unop).val.hom).app n ((F.map Y.1.unop X.1.unop).app n a)).val.app d α) x =
    (((relativeFunctorOverPre (G.obj X.1.unop).val.hom (η.val Y.1.unop)).app n
      ((G.map Y.1.unop X.1.unop).app n a)).val.app d α) x at h
  rw [relativeFunctorPost_apply, relativeFunctorOverPre_apply] at h
  change (((simplicialOverTestAction (Opposite.op (F.obj X.1.unop), X.2)
    (Opposite.op (F.obj Y.1.unop), Y.2)).app n
      ((relativeFunctorOverPre X.2.val.hom (η.val X.1.unop)).app n f,
        (F.map Y.1.unop X.1.unop).app n a, b)).val.app d α) x =
    (((relativeFunctorOverPre Y.2.val.hom (η.val Y.1.unop)).app n
      ((simplicialOverTestAction (Opposite.op (G.obj X.1.unop), X.2)
        (Opposite.op (G.obj Y.1.unop), Y.2)).app n
          (f, (G.map Y.1.unop X.1.unop).app n a, b))).val.app d α) x
  rw [relativeFunctorOverPre_apply]
  have hF := simplicialOverTestAction_apply
    (show SimplicialPairObject (SimplicialOverObject B)ᵒᵖ (LeftFibrationObject B) from
      (Opposite.op (F.obj X.1.unop), X.2))
    (Opposite.op (F.obj Y.1.unop), Y.2)
    ((relativeFunctorOverPre X.2.val.hom (η.val X.1.unop)).app n f)
    ((F.map Y.1.unop X.1.unop).app n a) b α x
  rw [relativeFunctorOverPre_apply] at hF
  have hG := simplicialOverTestAction_apply
    (show SimplicialPairObject (SimplicialOverObject B)ᵒᵖ (LeftFibrationObject B) from
      (Opposite.op (G.obj X.1.unop), X.2))
    (Opposite.op (G.obj Y.1.unop), Y.2)
    f ((G.map Y.1.unop X.1.unop).app n a) b α
    ((η.val Y.1.unop).left.app d x)
  exact hF.trans ((congrArg (fun z ↦ (b.val.app d α) ((f.val.app d α) z)) h).trans hG.symm)

/-- 豊穣関手の各値から全標的への相対 Hom を同じ二変数の共同族へ実現する。 -/
def simplicialOverJointTest {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {B : SSet.{u}} (F : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)) :
    SimplicialNerve (SimplicialPairObject Cᵒᵖ (LeftFibrationObject B)) ⟶ SpaceInfinity.{u} :=
  coherentNerveMap (simplicialOverTestBifunctor F)

/-- 前合成同値な各脚を持つ一つの自然な比較は、二変数の共同族の関手同型を与える。 -/
def SimplicialOverComparison.jointTestIso {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}} [Quasicategory B]
    {F G : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)}
    (η : SimplicialOverComparison F G)
    (h : ∀ X, IsPrecompositionEquivalence (η.val X).left) :
    FunctorIso (simplicialOverJointTest G) (simplicialOverJointTest F) :=
  kanEnrichedComparisonIso η.jointTestComparison
    (fun X ↦ relativeFunctorOverPre_isQCatEquivalence X.2.val.hom (η.val X.1.unop) (h _))

/-- 共同族は対象の対で実際の相対 Hom の Kan 複体を厳密に回収する。 -/
lemma simplicialOverJointTest_vertex {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}}
    (F : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)) (X : C)
    (q : LeftFibrationObject B) :
    (simplicialOverJointTest F).app (Opposite.op ⦋0⦌)
      (coherentNerveVertex (show SimplicialPairObject Cᵒᵖ (LeftFibrationObject B) from
        (Opposite.op X, q))) =
    spaceInfinityVertex ⟨relativeFunctorSpace q.val.hom (F.obj X).val.hom, inferInstance⟩ := by
  rw [spaceInfinityVertex_eq_coherent]
  exact coherentNerveMap_vertex (simplicialOverTestBifunctor F) _

/-- 始域を固定すると、共同族は既存の全標的の coherent な評価を回収する。 -/
lemma simplicialOverJointTest_right {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}}
    (F : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)) (X : C) :
    coherentNerveMap (simplicialPairRightInclusion (Opposite.op X) (LeftFibrationObject B)) ≫
      simplicialOverJointTest F = leftFibrationCoherentEvaluation (F.obj X).val := by
  rw [simplicialOverJointTest, ← coherentNerveMap_comp, simplicialOverTestBifunctor_right]
  rfl

/-- 共同比較の成分は、元の底上の比較に沿う実際の前合成そのもの。 -/
lemma SimplicialOverComparison.jointTestComparison_component {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C] {B : SSet.{u}}
    {F G : EnrichedFunctor SSet.{u} C (SimplicialOverObject B)}
    (η : SimplicialOverComparison F G) (X : C) (q : LeftFibrationObject B) :
    η.jointTestComparison.val (Opposite.op X, q) =
      relativeFunctorOverPre q.val.hom (η.val X) := rfl

end SerrePositivity.InfinityCategories
