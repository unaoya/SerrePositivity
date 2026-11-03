module
public import SerrePositivity.InfinityCategories.F1.CatInfinity.CoherentVertices

public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackProjections
public import SerrePositivity.InfinityCategories.F2.CatInfinity.QCatPullbackLimit

/-!
概要：lax pullback を頂点とする Cat_∞ 内の実際の極限錐。
方針：両端評価の持ち上げ性を QCat の豊穣極限判定へ適用する。
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

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：lax pullback を頂点とする Cat_∞ 内の実際の極限錐。
方針：両端評価の持ち上げ性を QCat の豊穣極限判定へ適用する。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
def laxPullbackDiagram (p : A ⟶ C) (q : B ⟶ C) : AsSmall.{u} WalkingCospan ⥤ QCat.{u} :=
  qCatPullbackDiagram
    (show qCatArrowObject C ⟶ qCatTensorObject C C from arrowEndpointPair C)
    (show qCatTensorObject A B ⟶ qCatTensorObject C C from p ⊗ₘ q)
/-- 概要：lax pullback を頂点とする Cat_∞ 内の実際の極限錐。
方針：両端評価の持ち上げ性を QCat の豊穣極限判定へ適用する。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
def laxPullbackOrdinaryCone (p : A ⟶ C) (q : B ⟶ C) : Cone (laxPullbackDiagram p q) :=
  qCatPullbackCone
    (show qCatArrowObject C ⟶ qCatTensorObject C C from arrowEndpointPair C)
    (show qCatTensorObject A B ⟶ qCatTensorObject C C from p ⊗ₘ q)
/-- 概要：lax pullback を頂点とする Cat_∞ 内の実際の極限錐。
方針：両端評価の持ち上げ性を QCat の豊穣極限判定へ適用する。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
def laxPullbackCone (p : A ⟶ C) (q : B ⟶ C) :
    JoinCone (HomotopyLimits.strictCoherentDiagram (laxPullbackDiagram p q)) :=
  HomotopyLimits.strictCoherentCone (laxPullbackOrdinaryCone p q)
/-- 概要：lax pullback を頂点とする Cat_∞ 内の実際の極限錐。
方針：両端評価の持ち上げ性を QCat の豊穣極限判定へ適用する。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
lemma laxPullbackCone_isLimit (p : A ⟶ C) (q : B ⟶ C) : IsLimitCone (laxPullbackCone p q) :=
  qCatPullbackInfinityCone_isLimit _ _ (arrowEndpointPair_kanEquivalenceLifting C)
/-- 概要：lax pullback を頂点とする Cat_∞ 内の実際の極限錐。
方針：両端評価の持ち上げ性を QCat の豊穣極限判定へ適用する。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
lemma laxPullbackCone_vertex (p : A ⟶ C) (q : B ⟶ C) :
    (laxPullbackCone p q).vertex = coherentVertex (laxPullbackObject p q) :=
  HomotopyLimits.strictCoherentCone_vertex _

end SerrePositivity.InfinityCategories.F2
