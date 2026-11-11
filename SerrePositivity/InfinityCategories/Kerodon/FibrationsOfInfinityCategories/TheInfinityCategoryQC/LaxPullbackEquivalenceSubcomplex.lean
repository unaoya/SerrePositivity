module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackLift
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration

/-!
概要：lax pullback の指定矢印が同値である対象の張る全部分複体。
方針：矢印射影で可逆 path の頂点条件を引き戻す。
規約：元の指定矢印の族を保持し、同値類だけに置き換えない。
使われ方：Tamme §1 Remark 7 の通常の引き戻しとの比較。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}}

/-- 概要：lax pullback の頂点の指定矢印が同値である条件。
方針：矢印射影を可逆 path の頂点条件へ合成する。
規約：p(a) から q(b) への元の矢印を使う。
使われ方：通常の引き戻しを張る対象の指定。 -/
def IsLaxEquivalenceVertex (p : A ⟶ C) (q : B ⟶ C)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q).app _ x)

/-- 概要：指定矢印が同値である頂点の張る全部分複体。
方針：全頂点が同値矢印条件を満たす単体を取る。
規約：周囲の lax pullback と同じ高次単体を保持する。
使われ方：Tamme §1 Remark 7 の全部分圏。 -/
def laxPullbackEquivalenceSubcomplex (p : A ⟶ C) (q : B ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) (IsLaxEquivalenceVertex p q)

/-- 概要：同値矢印の全部分複体は quasicategory。
方針：lax pullback の quasicategory 性と全部分複体の充填性を使う。
規約：元の三圏以外に充填条件を要求しない。
使われ方：通常の引き戻しを表す全部分 ∞ 圏。 -/
instance laxPullbackEquivalenceSubcomplex_quasicategory
    (p : A ⟶ C) (q : B ⟶ C) [Quasicategory A] [Quasicategory B] [Quasicategory C] :
    Quasicategory (laxPullbackEquivalenceSubcomplex p q : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- 概要：同値矢印の全部分複体から元の指定可逆 path を読む。
方針：矢印射影を可逆 path の全部分複体へ制限する。
規約：零単体の条件のみから全次数の族を構成する。
使われ方：catPullback への比較射の path 成分。 -/
def laxPullbackEquivalencePath (p : A ⟶ C) (q : B ⟶ C) :
    (laxPullbackEquivalenceSubcomplex p q : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
    ((laxPullbackEquivalenceSubcomplex p q).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q)
    (fun x ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x)

/-- 概要：制限した可逆 path の包含は元の矢印射影。
方針：全部分複体への lift の包含を計算する。
規約：射の厳密な等式。
使われ方：指定 path の保持と両端条件の照合。 -/
lemma laxPullbackEquivalencePath_ι (p : A ⟶ C) (q : B ⟶ C) :
    laxPullbackEquivalencePath p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι C =
      (laxPullbackEquivalenceSubcomplex p q).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
