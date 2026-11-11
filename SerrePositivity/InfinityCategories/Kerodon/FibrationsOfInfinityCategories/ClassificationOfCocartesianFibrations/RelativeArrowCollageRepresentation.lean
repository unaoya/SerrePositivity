module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeArrowCollageLeftFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinSmallness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallRepresentationExtension

/-!
概要：小さい全空間の相対射の区間実現を coherent な空間値図式で分類する。
方針：join と pullback の小ささを表現空間の可縮性へ渡す。
規約：底の小ささも相対射の可逆性も要求しない。
使われ方：非可逆な相対射を coherent な変換へ復元するための表現。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：小さい全空間の射の区間実現も各次数で小さい。
方針：join と区間との積の小ささを pullback に移す。
規約：終域への構造射やその底の小ささは不要。
使われ方：区間実現への表現の存在定理の適用。 -/
lemma relativeArrowCollage_obj_small {E F : SSet.{u + 1}}
    [∀ n, Small.{u} (E.obj n)] [∀ n, Small.{u} (F.obj n)]
    (f : E ⟶ F) (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 F)).obj n) := by
  have : Small.{u} (((Δ[1] : SSet.{u + 1}) ⊗ F).obj n) := by
    change Small.{u} ((Δ[1] : SSet.{u + 1}).obj n × F.obj n)
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullback_obj_small (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal F) n

/-- 概要：相対射の区間実現の表現空間は可縮 Kan。
方針：両端の left fibration 性と全空間の小ささを一般の表現定理に渡す。
規約：可逆でない射も含み底は任意の単体集合。
使われ方：射を復元する図式の存在と選択独立性。 -/
lemma relativeArrowCollageWitnessSpace_isContractibleKan {E F B : SSet.{u + 1}}
    [∀ n, Small.{u} (E.obj n)] [∀ n, Small.{u} (F.obj n)]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection_leftFibration p q f hf
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection f q)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection_leftFibration p q f hf
  have : ∀ n, Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 F)).obj n) :=
    relativeArrowCollage_obj_small f
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallTransportWitnessSpace_isContractibleKan _

/-- 概要：小さい全空間の相対射の区間実現は実際の coherent な表現を持つ。
方針：可縮な表現空間の頂点を実際の表現へ戻す。
規約：両端の表現を指定する前の絶対的な存在。
使われ方：非可逆変換の復元の入力。 -/
lemma relativeArrowCollageRepresentation_nonempty {E F B : SSet.{u + 1}}
    [∀ n, Small.{u} (E.obj n)] [∀ n, Small.{u} (F.obj n)]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection_leftFibration p q f hf
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection f q)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection_leftFibration p q f hf
  obtain ⟨v⟩ := (relativeArrowCollageWitnessSpace_isContractibleKan p q f hf).nonempty
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertexEquiv _).symm v⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
