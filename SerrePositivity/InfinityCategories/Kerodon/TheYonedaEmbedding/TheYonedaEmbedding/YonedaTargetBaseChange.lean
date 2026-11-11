module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChange

/-!
概要：Yoneda 写像の指定対象での前層を、第二変数を固定した twisted arrow 射影と比較する。
方針：実際の共同評価の制限を宇宙持ち上げ後の底変換と同定し、分類図式の底変換同型を使う。
規約：同じ yonedaInfinityMap の対象図式を保ち、独立した分類図式へ置き換えない。
使われ方：表現可能 right fibration との照合への接続。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- twisted arrow の第二変数を対象 c に固定する底の包含。 -/
def twistedArrowTargetInclusion {C : SSet.{u}} (c : C _⦋0⦌) : C.op ⟶ C.op ⊗ C :=
  lift (𝟙 C.op) (SSet.const c)

/-- 第二変数を固定した twisted arrow の全空間。 -/
def twistedArrowTarget {C : SSet.{u}} (c : C _⦋0⦌) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (twistedArrowTargetInclusion c)

/-- 同じ全空間から反転した元の底への射影。 -/
def twistedArrowTargetProjection {C : SSet.{u}} (c : C _⦋0⦌) :
    twistedArrowTarget c ⟶ C.op :=
  pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (twistedArrowTargetInclusion c)

/-- 第二変数を固定した実際の射影は left fibration。 -/
instance twistedArrowTargetProjection_leftFibration {C : SSet.{u}} [Quasicategory C]
    (c : C _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (twistedArrowTargetProjection c) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C))⟩

/-- 実際の前層の図式は、元の twisted arrow の分類図式を固定した第二変数へ制限したもの。 -/
lemma representablePresheafInfinity_eq_targetRestriction {C : SSet.{u}} [Quasicategory C]
    (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity c =
      (SSet.uliftFunctor.{u + 1, u}).map (twistedArrowTargetInclusion c) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C := by
  have h : lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj C.op))
      (SSet.const (ULift.up c)) ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1} C.op C).inv =
      (SSet.uliftFunctor.{u + 1, u}).map (twistedArrowTargetInclusion c) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun f ↦ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C) h)

/-- 同じ実際の前層は、第二変数を固定した射影そのものの分類図式と関手同型。 -/
def representablePresheafInfinity_targetIso {C : SSet.{u}} [Quasicategory C]
    (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram (twistedArrowTargetProjection c)) := by
  rw [representablePresheafInfinity_eq_targetRestriction]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (twistedArrowTargetInclusion c)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
