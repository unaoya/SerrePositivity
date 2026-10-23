module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.QCatTensorAndArrowObjects

/-!
概要：Fun(Δ¹,C) と両端評価による lax pullback 対象。
方針：Tamme の定義の strict pullback と inner fibration 性を使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：Fun(Δ¹,C) と両端評価による lax pullback 対象。
方針：Tamme の定義の strict pullback と inner fibration 性を使う。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
def laxPullback {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C) : SSet.{u} :=
  pullback (arrowEndpointPair C) (p ⊗ₘ q)
/-- 概要：Fun(Δ¹,C) と両端評価による lax pullback 対象。
方針：Tamme の定義の strict pullback と inner fibration 性を使う。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
instance laxPullback_quasicategory {A B C : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C] (p : A ⟶ C) (q : B ⟶ C) :
    Quasicategory (laxPullback p q) := by
  have : Quasicategory (A ⊗ B) := quasicategory_tensor A B
  exact inferInstanceAs (Quasicategory (pullback (arrowEndpointPair C) (p ⊗ₘ q)))
/-- 概要：Fun(Δ¹,C) と両端評価による lax pullback 対象。
方針：Tamme の定義の strict pullback と inner fibration 性を使う。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
def laxPullbackObject {A B C : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C] (p : A ⟶ C) (q : B ⟶ C) : QCat.{u} :=
  (⟨laxPullback p q, inferInstance⟩ : QuasicategoryObject.{u})

end SerrePositivity.InfinityCategories.F2
