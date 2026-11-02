module

public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanAnodyne
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanWeakFunctoriality
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakHomotopy
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakHomotopyInverse
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakWhitehead
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanSourceReplacement
public import SerrePositivity.InfinityCategories.HomotopyLimits.OppositeFibration
public import SerrePositivity.InfinityCategories.HomotopyLimits.OppositeKanHomotopy

/-!
概要：単体順序の反転は任意の単体集合間の弱ホモトピー同値を保つ。
方針：anodyne な Kan 単位を反転し、Kan 値の Whitehead 判定と二対三則を使う。
規約：元の二対象の Kan 性は不要。
使われ方：反転した Bousfield–Kan 重みの augmentation の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 概要：anodyne な射を反転しても anodyne。
方針：反転の自己随伴と Kan fibration の反転保存で持ち上げ性を移す。
規約：完全なモデル構造は使わない。使われ方：Kan 単位の反転。 -/
lemma anodyne_opFunctor_map {X Y : SSet.{u}} (f : X ⟶ Y) (hf : anodyneExtensions f) :
    anodyneExtensions (SSet.opFunctor.map f) := by
  intro E D p hp
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff p).mpr hp
  have h : HasLiftingProperty f (SSet.opFunctor.map p) :=
    hf _ ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance)
  exact (SSet.opEquivalence.toAdjunction.hasLiftingProperty_iff f p).mpr h

/-- 概要：連続 Kan 単位の反転も弱ホモトピー同値。
方針：反転した単位の anodyne 性を全 Kan 標的で検査する。
規約：元の対象に充填性は不要。使われ方：反転の弱同値保存への帰着。 -/
lemma continuousKanReplacementUnit_op_isWeakHomotopyEquivalence (X : SSet.{u}) :
    IsWeakHomotopyEquivalence (SSet.opFunctor.map (continuousKanReplacementUnit.app X)) := by
  intro Z _
  exact (homotopyEquivalence_pre_of_anodyne _
    (anodyne_opFunctor_map _ (continuousKanReplacementUnit_anodyne X)) Z).mapPiZero_bijective

/-- 概要：反転は任意の射の弱ホモトピー同値性を保つ。
方針：Kan 置換した射のホモトピー逆を反転し、単位の自然性で戻す。
規約：始域・終域の Kan 性を追加しない。使われ方：反転した coend の比較。 -/
lemma opposite_map_isWeakHomotopyEquivalence {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : IsWeakHomotopyEquivalence f) :
    IsWeakHomotopyEquivalence (SSet.opFunctor.map f) := by
  have hQ := continuousKanReplacement_map_isWeakHomotopyEquivalence f hf
  have hQop := oppositeKanHomotopyEquivalence hQ.isSimplicialHomotopyEquivalence
  have hn : f ≫ continuousKanReplacementUnit.app Y =
      continuousKanReplacementUnit.app X ≫ continuousKanReplacement.map f :=
    continuousKanReplacementUnit.naturality f
  apply (continuousKanReplacementUnit_op_isWeakHomotopyEquivalence Y).cancel_right
  rw [← CategoryTheory.Functor.map_comp, hn, CategoryTheory.Functor.map_comp]
  exact (continuousKanReplacementUnit_op_isWeakHomotopyEquivalence X).comp
    hQop.isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
