module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationFamilyRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeArrowFamilyRealization

/-!
概要：一般の二つの表現の間の相対射の族を変換空間への射として復元する。
方針：指定両端の collage の実現を curry し pointed な証拠と束ねる。
規約：次数 fiber の小ささのみを明示的に要求する。
使われ方：一般の straightening の写像空間への作用の構成。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：区間付きの底変換は結合子と可換。
方針：各次数の三つの成分で計算する。
規約：パラメーター K は最後の因子。
使われ方：復元した prism の射影の式を既存の族の表示へ移す。 -/
lemma parameterizedPrism_associator_naturality {E B : SSet.{u}}
    (p : E ⟶ B) (K : SSet.{u}) :
    (α_ (Δ[1] : SSet.{u}) E K).hom ≫ (Δ[1] ◁ (p ▷ K)) =
      ((Δ[1] ◁ p) ▷ K) ≫ (α_ Δ[1] B K).hom := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 概要：相対射の族は選択表現の分類図式の変換と pointed な実現を持つ。
方針：指定両端の collage の実現を変換空間へ curry する。
規約：底とパラメーターを小さく制限しない。
使われ方：全相対写像空間の普遍的な射の族を復元する。 -/
lemma transportRepresentationFamilyWitness_nonempty {E F B K : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers p) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers q)
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q)
    (f : E ⊗ K ⟶ F) (hf : f ≫ q = fst E K ≫ p) :
    Nonempty (Σ t : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace R.diagram S.diagram,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness R S t f) := by
  obtain ⟨H, W, h₀, h₁, hw₀, hw₁, hwp⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeArrowFamily_specified_coherent_realization_of_small_fibers p q f hf hp hq R S
  let t := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.coherentTransformationFamilyCurry R.diagram S.diagram H h₀ h₁
  refine ⟨⟨t, { prism := (α_ Δ[1] E K).hom ≫ W, source := ?_, target := ?_, projection := ?_ }⟩⟩
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.prismEndpoint_associator]
    exact hw₀
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.prismEndpoint_associator]
    exact hw₁
  · rw [Category.assoc, hwp, ← Category.assoc, parameterizedPrism_associator_naturality,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.coherentTransformationFamilyCurry_prism]

/-- 概要：相対射の族の coherent な復元とその証拠を同時に選ぶ。
方針：束ねた実現の非空性から一組を選ぶ。
規約：変換の族と pointed な証拠を別々に選ばない。
使われ方：写像空間の実際の比較射の定義。 -/
def transportRepresentationFamilyRecovery {E F B K : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers p) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers q)
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q)
    (f : E ⊗ K ⟶ F) (hf : f ≫ q = fst E K ≫ p) :
    Σ t : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace R.diagram S.diagram,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportRepresentationFamilyWitness R S t f :=
  Classical.choice (transportRepresentationFamilyWitness_nonempty hp hq R S f hf)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
