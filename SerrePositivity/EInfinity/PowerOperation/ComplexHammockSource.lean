module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.RightFrames
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelHammockLocalization
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.WeakNerveInverts
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.OrdinaryDerivedSource
public import SerrePositivity.KST.LocalizingInvariants.LocalizationFactorization

/-!
# 元の全複体の hammock の実局所化と既存 D(A) への比較

DAG XIII §2.2 の native な降下への前段。同じ実射影モデルと右 frame の族を使う。
比較の同値性はまだ主張せず、元の導来源を延長した比較と指定二胞体を作る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open scoped Simplicial
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.HA.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories (derivedInfinityCategory)
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open IsomorphismsAndIsofibrations (isInvertibleEdge_congr)
variable (A : Type u) [CommRing A]

/-- 構成済みの実射影弱同値を持つ、全複体の同じ相対圏。 -/
def complexRelativeCategory : RelativeCategory.{u + 1} := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact modelRelativeCategory (Complex A)

/-- 宇宙の表示だけを忘れる同じ通常の複体関手。 -/
abbrev complexRelativeDown : (complexRelativeCategory A).category ⥤ Complex A := AsSmall.down

/-- 同じ全複体の hammock の native nerve。 -/
abbrev complexHammockNerve := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockNerve (complexRelativeCategory A)

/-- 同じ hammock への指定局所化写像。 -/
abbrev complexHammockSource := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (complexRelativeCategory A)

lemma complexHammockSource_isLocalization :
    IsLocalization (complexHammockSource A) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (complexRelativeCategory A)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory_cofibrantlyGenerated A
  have := hasFunctorialFactorization_cofibration_trivialFibration
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A) (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A)
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelHammock_isLocalization (_root_.SerrePositivity.ComplexLimits.rightFrameFamily A)

/-- 異なる Hom 宇宙の通常図式を、同じ全複体の元の図式へ写す。 -/
def complexRelativeNerveDown : nerve (complexRelativeCategory A).category ⟶ nerve (Complex A) where
  app _ := ↾fun X => ((complexRelativeDown A).mapComposableArrows _).obj X

lemma complexRelativeNerveDown_mk₁ {X Y : (complexRelativeCategory A).category} (f : X ⟶ Y) :
    (complexRelativeNerveDown A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ ((complexRelativeDown A).map f) :=
  ComposableArrows.ext₁ rfl rfl (by simp [complexRelativeNerveDown])

/-- 元の通常導来源を、同じ宇宙表示の相対圏上で読む。 -/
def complexRelativeDerivedSource :
    nerve (complexRelativeCategory A).category ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A :=
  complexRelativeNerveDown A ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A

lemma complexRelativeDerivedSource_inverts :
    InvertsEdges (complexRelativeDerivedSource A) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (complexRelativeCategory A)) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges_inverts_of_arrows (complexRelativeCategory A)
  intro X Y f hf
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have hq : QuasiIso ((complexRelativeDown A).map f) := hf
  have h := _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource_map_weak A ((complexRelativeDown A).map f) hq
  apply (isInvertibleEdge_congr ?_).mp h
  change (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
    (ComposableArrows.mk₁ ((complexRelativeDown A).map f)) = _
  change (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
    (ComposableArrows.mk₁ ((complexRelativeDown A).map f)) =
    (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
      ((complexRelativeNerveDown A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f))
  rw [complexRelativeNerveDown_mk₁]

/-- 全圏局所化の普遍性で作る、既存 D(A) への実比較。 -/
def complexHammockDerivedComparison : complexHammockNerve A ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A :=
  KST.LocalizingInvariants.localizationDescend _ _ (complexHammockSource_isLocalization A)
    (complexRelativeDerivedSource A) (complexRelativeDerivedSource_inverts A)

/-- 比較は元の全複体の導来源へ、指定全関手の同型で戻る。 -/
def complexHammockDerivedComparison_sourceIso :
    FunctorIso (complexHammockSource A ≫ complexHammockDerivedComparison A)
      (complexRelativeDerivedSource A) :=
  KST.LocalizingInvariants.localizationDescendIso _ _ (complexHammockSource_isLocalization A)
    (complexRelativeDerivedSource A) (complexRelativeDerivedSource_inverts A)

end SerrePositivity.EInfinity.PowerOperation
