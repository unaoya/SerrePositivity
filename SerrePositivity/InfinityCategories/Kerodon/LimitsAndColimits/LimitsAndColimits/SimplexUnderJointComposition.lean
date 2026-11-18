module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeSectionBaseChangePasting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexUnderBaseChangeNaturality

/-!
概要：underへの制限と定義域への制限の三角形を、元の指定共同実現同型の合成式にする。
方針：自然変換の合成を一般のjoint比較で先に計算し、指定under変換に適用する。
規約：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）の構成の照合。
  全添字と全left fibrationsを同時に保ち、点ごとの同型は集めない。
使われ方：S8のP3-B2e、表現の底変換の指定比較への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

private def overPreJoint {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A T : Jᵒᵖ ⥤ Over B} (η : A ⟶ T) :
    KanEnrichedDiagramComparison (relativeSectionEnrichedDiagram T)
      (relativeSectionEnrichedDiagram A) where
  component j := relativeFunctorOverPreComparison (η.app (Opposite.op j))
  naturality f p := (relativeSectionDiagramComparison η p).naturality f

private lemma overPreJoint_iso {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A T : Jᵒᵖ ⥤ Over B} (η : A ⟶ T)
    (hη : ∀ j (p : LeftFibrationObject B),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom (η.app (Opposite.op j)))) :
    relativeSectionRealizationComparisonIso η hη = (overPreJoint η).realizationIso hη := by
  rfl

private lemma overPreJoint_comp {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A T Z : Jᵒᵖ ⥤ Over B} (η : A ⟶ T) (θ : T ⟶ Z) :
    overPreJoint (η ≫ θ) = jointComparisonTrans (overPreJoint θ) (overPreJoint η) := by
  apply jointComparison_ext
  intro j p
  change relativeFunctorOverPre p.val.hom (η.app (Opposite.op j) ≫ θ.app (Opposite.op j)) = _
  exact relativeFunctorOverPre_comp _ _ _

private lemma overPreJoint_comp_iso {B : SSet.{u}} {J : Type u} [Category.{u} J]
    {A T Z : Jᵒᵖ ⥤ Over B} (η : A ⟶ T) (θ : T ⟶ Z) (γ : A ⟶ Z)
    (hγ : γ = η ≫ θ)
    (hη : ∀ j (p : LeftFibrationObject B),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom (η.app (Opposite.op j))))
    (hθ : ∀ j (p : LeftFibrationObject B),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom (θ.app (Opposite.op j))))
    (hγe : ∀ j (p : LeftFibrationObject B),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom (γ.app (Opposite.op j)))) :
    relativeSectionRealizationComparisonIso θ hθ ≪≫
      relativeSectionRealizationComparisonIso η hη =
      relativeSectionRealizationComparisonIso γ hγe := by
  subst γ
  rw [overPreJoint_iso, overPreJoint_iso, overPreJoint_iso]
  exact (jointRealizationIso_trans (overPreJoint θ) (overPreJoint η) hθ hη
    (jointComparisonTrans_isQCatEquivalence (overPreJoint θ) (overPreJoint η) hθ hη)).trans
      (jointRealizationIso_congr (overPreJoint_comp η θ).symm _ _)

/-- 二つの元の切断制限の指定同型の合成は、元の定義域への制限の指定同型。
HTT §3.3.2・Kerodon Corollary 5.6.0.6（Tag 028T）の指定構成の法則を、
同じUnder.postの自然変換の三角形に沿って照合する。 -/
@[cite HTT "3.3.2" (partial := special) "単体圏underの全族の切断制限同型の合成則。"]
lemma transportSimplexUnderRealization_baseChange_composition : ∀ {B D : SSet.{u}} (k : D ⟶ B),
  let ρ := transportSimplexUnderBaseChangeTransformation k
  let ηD := Functor.whiskerRight (transportSimplexUnderDomainTransformation D) (Over.map k)
  let ηB := Functor.whiskerLeft (transportSimplexFunctor k).op
      (transportSimplexUnderDomainTransformation B) ≫
    eqToHom (transportSimplexDomainFunctor_baseChange k)
  ∀ (hηB : ∀ j (p : LeftFibrationObject B),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom (ηB.app (Opposite.op j))))
    (hηD : ∀ j (p : LeftFibrationObject B),
      IsQCatEquivalence (relativeFunctorOverPre p.val.hom (ηD.app (Opposite.op j)))),
  relativeSectionRealizationComparisonIso ηB hηB ≪≫
    relativeSectionRealizationComparisonIso ρ
      (fun j p => transportSimplexUnderBaseChangeComparison_isQCatEquivalence k j p) =
    relativeSectionRealizationComparisonIso ηD hηD := by
  intro B D k
  dsimp only
  intro hηB hηD
  exact overPreJoint_comp_iso _ _ _ (transportSimplexUnderTransformation_baseChange k)
    (fun j p => transportSimplexUnderBaseChangeComparison_isQCatEquivalence k j p) hηB hηD
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
