module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackEquivalenceIso
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping

/-!
概要：同値矢印の全部分圏との比較同型の射影と path の保持。
方針：構成した比較射の三成分の等式を公開同型へ移す。
規約：元の二射影と元の指定 path を用いる。
使われ方：Tamme §1 Remark 7 と安定 ∞ 圏への接続。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}}

/-- 概要：比較同型は元の lax pullback への射を保つ。
方針：全部分複体への lift の包含を読む。
規約：包含への合成を元の比較射と厳密に同定する。
使われ方：二射影と矢印の三成分の比較。 -/
lemma catPullbackEquivalenceSubcomplexIso_ι (p : A ⟶ C) (q : B ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackEquivalenceSubcomplexIso p q).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackEquivalenceSubcomplex p q).ι = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax p q := rfl

/-- 概要：比較同型は元の第一射影を保つ。
方針：包含の等式と比較射の第一成分を使う。
規約：元の A への射の等式。
使われ方：全部分圏による通常の引き戻しの表示。 -/
lemma catPullbackEquivalenceSubcomplexIso_fst (p : A ⟶ C) (q : B ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackEquivalenceSubcomplexIso p q).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackEquivalenceSubcomplex p q).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst p q := by
  rw [← Category.assoc, catPullbackEquivalenceSubcomplexIso_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax_fst]

/-- 概要：比較同型は元の第二射影を保つ。
方針：包含の等式と比較射の第二成分を使う。
規約：元の B への射の等式。
使われ方：全部分圏による通常の引き戻しの表示。 -/
lemma catPullbackEquivalenceSubcomplexIso_snd (p : A ⟶ C) (q : B ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackEquivalenceSubcomplexIso p q).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackEquivalenceSubcomplex p q).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd p q := by
  rw [← Category.assoc, catPullbackEquivalenceSubcomplexIso_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax_snd]

/-- 概要：比較同型は元の指定可逆 path を保つ。
方針：比較射の path の等式を使う。
規約：全パラメータの実際の path を比較する。
使われ方：Cat_∞ の引き戻し錐との指定可換性の比較。 -/
lemma catPullbackEquivalenceSubcomplexIso_path (p : A ⟶ C) (q : B ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackEquivalenceSubcomplexIso p q).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackEquivalencePath p q =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath p q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToEquivalenceSubcomplex_path p q

/-- 概要：同値矢印の全部分複体の包含は写像空間上で充満忠実。
方針：全部分複体の一般の pinched 写像空間比較を使う。
規約：h の充満忠実性だけに弱めない。
使われ方：通常の引き戻しの全部分 ∞ 圏としての表示。 -/
lemma laxPullbackEquivalenceSubcomplex_isFullyFaithful (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackEquivalenceSubcomplex p q).ι :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
