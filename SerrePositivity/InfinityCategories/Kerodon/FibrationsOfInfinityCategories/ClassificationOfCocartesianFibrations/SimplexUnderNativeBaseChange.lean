module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionCoefficientValues
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeSectionBaseChangeValue
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedRealizationValueHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoTransposeEvaluation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorIsoCurryComposition

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexSectionNativeBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningNativeCoefficients
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexUnderBaseChangeNaturality

/-!
概要：元の単体切断の底変換とunderへの制限の指定長方形を照合する。
方針：元の定義域等式の移送をHEqに分け、既存の制限の合成と底変換の自然性を適用する。
規約：HTT §3.3.2・Kerodon §5.6（Tag 028T）の指定構成の特殊な合成則。
使われ方：P3-C1PNU、初頂点の指定比較の長方形の上半分。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance simplexUnderNative_left {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

private lemma cast_heq.{v} {A B : Sort v} (h : A = B) (a : A) : HEq (Eq.mp h a) a := by
  cases h
  rfl

private lemma comp_heq.{v, w} {C : Type v} [Category.{w} C]
    {a b c a' b' c' : C} (ha : a = a') (hb : b = b') (hc : c = c')
    (f : a ⟶ b) (f' : a' ⟶ b') (g : b ⟶ c) (g' : b' ⟶ c')
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  subst a' b' c'
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl

private lemma restriction_transport_heq {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A T T' : Jᵒᵖ ⥤ Over B} (η : A ⟶ T) (h : T = T')
    (p : LeftFibrationObject B) :
    HEq (relativeSectionDiagramComparison (η ≫ eqToHom h) p)
      (relativeSectionDiagramComparison η p) := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]
  rfl

private lemma restriction_comp {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A T Z : Jᵒᵖ ⥤ Over B} (η : A ⟶ T) (θ : T ⟶ Z)
    (p : LeftFibrationObject B) :
    relativeSectionDiagramComparison (η ≫ θ) p =
      relativeSectionDiagramComparison θ p ≫ relativeSectionDiagramComparison η p := by
  apply NatTrans.ext
  funext j
  exact relativeFunctorOverPre_comp _ _ _

/-- 元のunder三角形と底変換の自然性による、指定長方形の合成則。
HTT §3.3.2・Kerodon Tag 028Tの構成を、この相対切断模型に特殊化した照合。 -/
@[cite HTT "3.3.2" (partial := special) "相対切断のunder制限と底変換の指定長方形。"]
lemma simplexUnderNativeBaseChange_square :
    ∀ {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    simplexSectionNativeBaseChange p k ≫
      Functor.whiskerLeft (transportSimplexFunctor k)
        ((nativeUnderJointComparison B).app (leftFibrationObjectOf p)) ≫
      relativeSectionDiagramComparison (transportSimplexUnderBaseChangeTransformation k)
        (leftFibrationObjectOf p) =
    (nativeUnderJointComparison D).app (leftFibrationObjectOf (pullback.snd p k)) ≫
      (relativeSectionBaseChangeComparison k (transportSimplexUnderDomains D)).app
        (leftFibrationObjectOf p) := by
  intro E B D p hp k
  let H := transportSimplexFunctor k
  let η := transportSimplexUnderDomainTransformation B
  let ηB := Functor.whiskerLeft H.op η ≫ eqToHom (transportSimplexDomainFunctor_baseChange k)
  let ρ := transportSimplexUnderBaseChangeTransformation k
  let β := (relativeSectionBaseChangeComparison k (transportSimplexDomainFunctor D)).app
    (leftFibrationObjectOf p)
  let U := Functor.whiskerLeft H ((nativeUnderJointComparison B).app (leftFibrationObjectOf p))
  have hβ : HEq β (simplexSectionNativeBaseChange p k) := by
    unfold simplexSectionNativeBaseChange
    exact (cast_heq _ _).symm
  have hU : HEq (relativeSectionDiagramComparison ηB (leftFibrationObjectOf p)) U :=
    restriction_transport_heq (Functor.whiskerLeft H.op η)
      (transportSimplexDomainFunctor_baseChange k) (leftFibrationObjectOf p)
  have he := comp_heq rfl
    (congrArg (fun T => T ⋙ kanObjectForget) (simplexSectionNativeTarget_eq p k)) rfl
    β (simplexSectionNativeBaseChange p k)
    (relativeSectionDiagramComparison ηB (leftFibrationObjectOf p)) U hβ hU
  have hr : relativeSectionDiagramComparison ηB (leftFibrationObjectOf p) ≫
      relativeSectionDiagramComparison ρ (leftFibrationObjectOf p) =
      relativeSectionDiagramComparison
        (Functor.whiskerRight (transportSimplexUnderDomainTransformation D) (Over.map k))
        (leftFibrationObjectOf p) := by
    rw [← restriction_comp]
    exact congrArg (fun η => relativeSectionDiagramComparison η (leftFibrationObjectOf p))
      (transportSimplexUnderTransformation_baseChange k).symm
  rw [← Category.assoc, ← eq_of_heq he, Category.assoc, hr]
  apply NatTrans.ext
  funext j
  exact (SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorBaseChangeForward_overPre
    p k ((transportSimplexUnderDomainTransformation D).app (Opposite.op j))).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
