module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanFibrationTools
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.QuasicategoryCore
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EquivalenceLiftingInvertible
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PathReplacementLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CoreRightFibration
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：圏論的同値の右持ち上げ条件と可逆 path 置換の core の Kan fibration 性。
方針：B4 の可逆辺の持ち上げを再利用し、core の右ファイブレーションを全ホーンへ移す。
規約：既存の SSet の Fibration クラスを使い、モデル圏の追加仮定を置かない。
使われ方：Cat_∞ の引き戻しを全試験関手 core の homotopy pullback として比較する。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]

/-- 概要：単射な圏論的同値を右に持ち上げる関手の core は Kan fibration。
方針：inner 性と終点指定の可逆辺の持ち上げを取り出し、core の右ホーンを充填する。
規約：主張する充填性は元の指定関手の core 自体に対するもの。
使われ方：path 置換で得られる全試験関手空間の一脚の充填性。 -/
@[kerodon 01EZ]
lemma coreMap_fibration_of_kanEquivalenceLifting (p : X ⟶ Y)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p) : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap p) := by
  have := hp.innerFibration
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.coreMap_rightFibration_of_invertibleTargetLifting p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EquivalenceLifting.invertibleTargetLifting hp)
  infer_instance

/-- 概要：任意の関手の可逆 path 置換の終点写像の core は Kan fibration。
方針：B4 の path 置換の右持ち上げ定理を core の充填性へ移す。
規約：元の関手 p の充填性は仮定しない。
使われ方：Cat_∞ の引き戻しの置換された一脚の空間の引き戻し。 -/
instance corePathReplacementMap_fibration (p : X ⟶ Y) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p)) :=
  coreMap_fibration_of_kanEquivalenceLifting _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.kanEquivalenceLifting_equivalencePathReplacementMap p)

/-- 概要：path 置換の後合成は任意の試験 K の関手 core でも Kan fibration を与える。
方針：圏論的同値の右持ち上げ条件の内部 Hom による保存を適用する。
規約：内部 Hom を取ってから置換する場合と、置換してから取る場合を区別する。
使われ方：実際の Cat_∞ の錐の全ての豊穣 Hom の fibration 条件。 -/
instance corePathReplacementMap_internalHom_fibration (K : SSet.{u}) (p : X ⟶ Y) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p))) :=
  coreMap_fibration_of_kanEquivalenceLifting _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.internalHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.kanEquivalenceLifting_equivalencePathReplacementMap p) K)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
