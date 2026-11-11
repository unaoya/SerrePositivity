module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinMapInnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InnerProductProjection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinBaseProjection

/-!
概要：inner fibration の相対 join の底への射影は inner fibration。
方針：join の inner fibration を prism へ底変換し、第二射影に合成する。
規約：共通の底の quasicategory 性は不要。
使われ方：fiber ごとの余錐の全空間を相対指数で扱う前提。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：quasicategory を第一因子に持つ直積の第二射影は inner fibration。
方針：対称同型で第一射影の既存結果に帰着する。
規約：第二因子の充填性は要求しない。
使われ方：区間付き底から底への射影。 -/
instance kanInnerFibration_productSnd (X Y : SSet.{u}) [Quasicategory X] :
    InnerFibration (snd X Y) := by
  have hi : innerFibrations (β_ X Y).hom :=
    MorphismProperty.of_isIso innerFibrations _
  have hc := innerFibrations.comp_mem _ _ hi (InnerFibration.mem (q := fst Y X))
  rw [braiding_hom_fst] at hc
  exact ⟨hc⟩

/-- 概要：二つの inner fibration の相対 join の底への射影は inner fibration。
方針：joinMap の底変換を区間付き底の第二射影に合成する。
規約：両因子の射も共通の底も任意の宇宙 u の単体集合。
使われ方：相対 join 上の関手の族の cartesian 輸送を構成する準備。 -/
instance kanRelativeJoinBaseProjection_innerFibration {X Y S : SSet.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [InnerFibration f] [InnerFibration g] :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection f g) := by
  have hi : innerFibrations (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S)) :=
    innerFibrations.pullback_snd _ _ (InnerFibration.mem (q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g))
  exact ⟨innerFibrations.comp_mem _ _ hi
    (InnerFibration.mem (q := snd (Δ[1] : SSet.{u}) S))⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
