module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackEquivalenceSubcomplex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackLift

/-!
概要：通常の引き戻し候補から lax pullback への指定データを保つ射。
方針：元の二射影と可逆 path の包含から厳密な lift を作る。
規約：全パラメータの path と両射影を等式として保持する。
使われ方：Tamme §1 Remark 7 の全部分圏への比較。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}}

/-- 概要：通常の引き戻し候補から lax pullback への比較射。
方針：可逆 path の包含を指定矢印として使う。
規約：任意の単体集合間の二射に対して構成する。
使われ方：同値矢印の全部分圏への分解。 -/
def catPullbackToLax (p : A ⟶ C) (q : B ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift p q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst p q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι C)
    (by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint, Category.assoc] using _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackPath_zero p q)
    (by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint, Category.assoc] using _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackPath_one p q)

/-- 概要：比較射は元の指定 path の包含を矢印成分に持つ。
方針：lax pullback への lift の第一成分を計算する。
規約：実際の path の等式。
使われ方：同値矢印条件と path の保持。 -/
lemma catPullbackToLax_arrow (p : A ⟶ C) (q : B ⟶ C) :
    catPullbackToLax p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_arrow ..

/-- 概要：比較射は第一射影を保つ。
方針：lift の第一の入力成分を計算する。
規約：元の A への射の等式。
使われ方：全部分圏との比較の第一成分。 -/
lemma catPullbackToLax_fst (p : A ⟶ C) (q : B ⟶ C) :
    catPullbackToLax p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst p q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_fst ..

/-- 概要：比較射は第二射影を保つ。
方針：lift の第二の入力成分を計算する。
規約：元の B への射の等式。
使われ方：全部分圏との比較の第二成分。 -/
lemma catPullbackToLax_snd (p : A ⟶ C) (q : B ⟶ C) :
    catPullbackToLax p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd p q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_snd ..

/-- 概要：比較射の全頂点は同値矢印条件を満たす。
方針：元の可逆 path の頂点条件を矢印成分の等式で輸送する。
規約：標的の quasicategory 性を要求しない。
使われ方：全部分複体への比較射の持ち上げ。 -/
lemma catPullbackToLax_vertex (p : A ⟶ C) (q : B ⟶ C)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsLaxEquivalenceVertex p q ((catPullbackToLax p q).app _ x) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
    ((catPullbackToLax p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q).app _ x)
  rw [catPullbackToLax_arrow]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath p q).app _ x)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
