module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsofibrationCriterion
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：単射な圏論的同値の右持ち上げ条件の相対内部 Hom による保存。
方針：二変数随伴で持ち上げ問題を pushout-product に移す。
規約：固定する図式は任意の単射で指定する。
使われ方：元の図式を固定する関手の同値の厳密な持ち上げ。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：右持ち上げ条件は単射による相対内部 Hom の比較へ移る。
方針：右因子の単射な前合成同値の pushout-product は再び単射な前合成同値。
規約：始域・標的と固定図式のパラメータに quasicategory 性を要求しない。
使われ方：指定部分と標的の像を同時に保つ同値の持ち上げ。 -/
@[kerodon 01F1, kerodon 01G3]
lemma EquivalenceLifting.relativeInternalHom {A B D E : SSet.{u}}
    {U : D ⟶ E} (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U) (i : A ⟶ B) [Mono i]
    (sq' : CategoryTheory.MonoidalClosed.internalHom.PullbackObjObj i U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting sq'.π := by
  intro K L j hm hj
  have : Mono j := hm
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  exact hU sq.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.mono_pushoutObjObj_ι i j sq) (hj.pushoutObjObj_right i sq)

/-- 概要：inner 性と可逆辺の持ち上げは相対内部 Hom に右持ち上げ条件を供給する。
方針：isofibration の判定で右持ち上げへ移し、相対内部 Hom の保存を使う。
規約：D・E のみ quasicategory、図式の指定は任意の単射。
使われ方：標準 isofibration 上の関手の指定部分固定の厳密化。 -/
lemma kanRelativeInternalHom_lifting_of_inner_of_targetLifting {A B D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTargetLifting U) (i : A ⟶ B) [Mono i]
    (sq' : CategoryTheory.MonoidalClosed.internalHom.PullbackObjObj i U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting sq'.π := by
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U := by
    intro K L j hm hj
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceLifting_of_innerFibration_of_targetLifting U hU j hm hj
  intro K L j hm hj
  exact EquivalenceLifting.relativeInternalHom hl i sq' j hm hj

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
