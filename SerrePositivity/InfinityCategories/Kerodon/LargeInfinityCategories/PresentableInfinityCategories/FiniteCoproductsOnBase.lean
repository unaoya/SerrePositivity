module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaYonedaFiniteCoproducts

/-!
概要：元の小さい底上の有限余積保存を、指定した宇宙持ち上げ後の全関手で表す。
方針：元の全有限離散図式と元の普遍余錐を量化する。
規約：空添字も含め、元の小さい底で判定する。
使われ方：Yoneda 制限上の有限余積保存による全小余極限保存判定。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の小さい底の全有限余積を指定した全関手が保存する条件。
方針：元の有限離散図式の native な普遍余錐の宇宙持ち上げの像を量化する。
規約：元の小さい底と空添字を保持する。
使われ方：P_Σ Yoneda 制限上の有限条件。 -/
def PreservesFiniteCoproductsOnBase {C : SSet.{u}} {D : SSet.{u + 1}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) : Prop :=
  ∀ (I : Type u) [Finite I] (p : nerve (Discrete I) ⟶ C) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u, u + 1} c))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
