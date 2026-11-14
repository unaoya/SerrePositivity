module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatTensorAndArrowObjects
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：Fun(Δ¹,C) と両端評価による lax pullback 対象。
方針：Tamme の定義の strict pullback と inner fibration 性を使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：Fun(Δ¹,C) と両端評価による lax pullback 対象。
方針：Tamme の定義の strict pullback と inner fibration 性を使う。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
@[kerodon 01KF]
def laxPullback {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair C) (p ⊗ₘ q)
/-- 概要：Fun(Δ¹,C) と両端評価による lax pullback 対象。
方針：Tamme の定義の strict pullback と inner fibration 性を使う。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
@[kerodon 01KH]
instance laxPullback_quasicategory {A B C : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C] (p : A ⟶ C) (q : B ⟶ C) :
    Quasicategory (laxPullback p q) := by
  have : Quasicategory (A ⊗ B) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategory_tensor A B
  exact inferInstanceAs (Quasicategory (pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair C) (p ⊗ₘ q)))
/-- 概要：Fun(Δ¹,C) と両端評価による lax pullback 対象。
方針：Tamme の定義の strict pullback と inner fibration 性を使う。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
def laxPullbackObject {A B C : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C] (p : A ⟶ C) (q : B ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} :=
  (⟨laxPullback p q, inferInstance⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u})

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Tamme "Def 5"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback
attribute [cite Tamme "Eq (5)"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback
