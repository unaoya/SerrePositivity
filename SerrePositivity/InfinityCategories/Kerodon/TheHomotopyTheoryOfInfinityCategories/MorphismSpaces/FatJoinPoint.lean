module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor

/-!
概要：二つの点の fat join と通常の join の比較の同型性。
方針：両端の射影が同型なので円柱の pushout 包含も同型であることを使う。
規約：この基本例を任意の単体集合の比較の完成とは数えない。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の零次元の基本例。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：二つの標準零単体の fat join の円柱包含は同型。
方針：二つの pushout で貼る射影が同型であることを使う。
規約：両因子が標準零単体の場合。
使われ方：Kerodon §4.6.2（Tag 01HM） の点の fat join。 -/
instance isIso_fatJoinCylinder_point :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u})) := by
  have : IsIso (pushout.inl (SSet.ι₀ (X := (Δ[0] : SSet.{u})) ▷ (Δ[0] : SSet.{u}))
      (fst (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}))) :=
    (IsPushout.of_hasPushout _ _).isIso_inl_of_isIso
  have : IsIso (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageEnd (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}))
      (snd (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}))) :=
    (IsPushout.of_hasPushout _ _).isIso_inl_of_isIso
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder
  infer_instance

/-- 概要：二つの点の円柱から通常の join への比較は同型。
方針：標準単体の join の同型と点との直積の比較の同型を合成する。
規約：両因子が標準零単体の場合。
使われ方：Kerodon §4.6.2（Tag 01HM） の最小の比較。 -/
instance isIso_joinCylinderMap_point :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u})) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap
  infer_instance

/-- 概要：二つの点の fat join から join への比較は同型。
方針：円柱包含を消去して比較の同型性を得る。
規約：一般の fat join 比較の同値性とは区別する。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の零次元の基本例。 -/
instance isIso_fatJoinComparison_point :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u})) :=
  IsIso.of_isIso_fac_left (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_comparison _ _)

/-- 概要：二つの点の fat join の比較は前合成の同値条件を満たす。
方針：比較が厳密な同型であることを使う。
規約：一般の二因子についての主張は未完了。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の基本例。 -/
lemma isPrecompositionEquivalence_fatJoinComparison_point :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u})) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u})))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
