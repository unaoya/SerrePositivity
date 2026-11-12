module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.CatPullback

/-!
概要：引き戻し候補の可逆 path の端点と、指定 path を保つ全パラメータの lift。
方針：二重の引き戻しの厳密な普遍性を二回使う。
規約：Cat_∞ の極限の普遍性と単体集合の厳密な lift は区別する。
使われ方：関手 ∞ 圏と引き戻し候補の比較。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C T : SSet.{u}}

/-- 概要：候補の指定 path の始点は第一射影の像。
方針：内側の引き戻しの可換性を使う。
規約：元の関手 p を保持する厳密な射の等式。
使われ方：第一の脚を固定した path の持ち上げ。 -/
lemma catPullbackPath_zero (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint C 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst p q ≫ p := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection,
    Category.assoc, pullback.condition]

/-- 概要：候補の指定 path の終点は第二射影の像。
方針：外側の引き戻しの可換性を使う。
規約：元の関手 q を保持する厳密な射の等式。
使われ方：第二の脚を固定した path の持ち上げ。 -/
lemma catPullbackPath_one (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint C 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd p q ≫ q := by
  change pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) q ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p = _
  exact pullback.condition

/-- 概要：二つの関手と両端を固定した指定可逆 path を候補へ持ち上げる。
方針：まず置換への lift を作り、終点条件を使って外側へ持ち上げる。
規約：パラメータ T は任意の単体集合でよい。
使われ方：引き戻し候補の関手空間の各次数の構成。 -/
def catPullbackLift (p : A ⟶ C) (q : B ⟶ C)
    (a : T ⟶ A) (b : T ⟶ B) (h : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath C)
    (h0 : h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint C 0 = a ≫ p)
    (h1 : h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint C 1 = b ≫ q) : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q :=
  pullback.lift (pullback.lift h a h0) b (by
    change pullback.lift h a h0 ≫ pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint C 1 = _
    rw [pullback.lift_fst_assoc]
    exact h1)

/-- 概要：指定 path による lift の第一射影は元の関手。
方針：二重の lift の第二射影を順に計算する。
規約：元の a を厳密に保持する。
使われ方：関手空間比較の第一成分。 -/
lemma catPullbackLift_fst (p : A ⟶ C) (q : B ⟶ C) (a : T ⟶ A) (b : T ⟶ B) (h) (h0) (h1) :
    catPullbackLift p q a b h h0 h1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst p q = a := by
  simp [catPullbackLift, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection]

/-- 概要：指定 path による lift の第二射影は元の関手。
方針：外側の lift の第二射影を計算する。
規約：元の b を厳密に保持する。
使われ方：関手空間比較の第二成分。 -/
lemma catPullbackLift_snd (p : A ⟶ C) (q : B ⟶ C) (a : T ⟶ A) (b : T ⟶ B) (h) (h0) (h1) :
    catPullbackLift p q a b h h0 h1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd p q = b := by
  simp [catPullbackLift, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd]

/-- 概要：指定 path による lift の path 成分は元の指定 path。
方針：二重の lift の第一射影を順に計算する。
規約：path の類だけでなく、実際の全パラメータの族を保持する。
使われ方：関手空間比較の比較 path 成分。 -/
lemma catPullbackLift_path (p : A ⟶ C) (q : B ⟶ C) (a : T ⟶ A) (b : T ⟶ B) (h) (h0) (h1) :
    catPullbackLift p q a b h h0 h1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath p q = h := by
  simp [catPullbackLift, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath]

/-- 概要：候補への射は二射影と実際の path 成分で決まる。
方針：二重の引き戻しの射の外延性を順に使う。
規約：可換性の類の一致だけに条件を弱めない。
使われ方：関手 ∞ 圏の比較射の逆条件の検証。 -/
lemma catPullback_hom_ext (p : A ⟶ C) (q : B ⟶ C) {f g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q}
    (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst p q = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackFst p q)
    (hs : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd p q = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackSnd p q)
    (hh : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath p q = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackPath p q) : f = g := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact hh
    · exact hf
  · exact hs

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
