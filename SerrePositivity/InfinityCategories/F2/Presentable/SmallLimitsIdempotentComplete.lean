module

public import SerrePositivity.InfinityCategories.F2.Presentable.EquivalenceSmallLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.Idempotent.IdemUniverse
public import SerrePositivity.InfinityCategories.F2.Idempotent.StrongSplittingLimitExistence
public import SerrePositivity.InfinityCategories.F2.Idempotent.FibrationComplete
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LimitColimitOpposite
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening

/-!
概要：小極限を持つ元の圏と、その空間値関手の全空間の冪等完備性。
方針：全 Idem 図式を小さい宇宙の同じ形状へ戻して極限を取り、強い分裂を得る。
規約：元の全 coherent 冪等図式を分裂し、ホモトピー圏だけの分裂に弱めない。
使われ方：余表現可能性の解関手の retract の分裂。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：小極限を持つ元の圏は全 coherent 冪等図式の強い分裂を持つ。
方針：Idem の厳密な宇宙変更を通して元の小極限の存在を適用する。
規約：対象と元の coherent 図式を保持する。
使われ方：解対象の retract を元の圏で分裂する。 -/
lemma HasSmallLimits.isIdempotentComplete {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits C) : Idempotent.IsIdempotentComplete C := by
  apply (Idempotent.isIdempotentComplete_iff_hasLimits C).mpr
  intro d
  apply (F1B.kanHasLimit_iff_restrict_of_isIso d
    Idempotent.idemShapeUniverseIso.{u, u + 1}.hom).mpr
  exact hC Idempotent.IdemShape _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits export _root_.SerrePositivity.InfinityCategories.F2.Presentable.HasSmallLimits (isIdempotentComplete)

/-- 概要：小極限を持つ底上の空間値関手の全空間は冪等完備。
方針：元の底の冪等完備性を左ファイブレーションに沿って持ち上げる。
規約：関手の極限保存性はこの分裂には要求しない。
使われ方：余表現可能性の全解における coherent retract の分裂。 -/
lemma unstraightening_isIdempotentComplete_of_smallLimits
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits C)
    (F : C ⟶ SpaceInfinity.{u}) : Idempotent.IsIdempotentComplete (leftUnstraightening F) :=
  Idempotent.isIdempotentComplete_of_leftFibration (leftUnstraighteningProjection F)
    hC.isIdempotentComplete

end SerrePositivity.InfinityCategories.F2.Presentable
