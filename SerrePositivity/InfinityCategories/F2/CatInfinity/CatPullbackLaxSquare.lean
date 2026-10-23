module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackToLax
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：通常の引き戻しは lax pullback の可逆 path による引き戻し。
方針：元の catPullback を頂点とする厳密な引き戻し錐の普遍性を証明する。
規約：矢印射影と可逆 path の包含を指定された射として保持する。
使われ方：Tamme §1 Remark 7 の可逆矢印への制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}}

/-- 概要：元の候補を頂点とする可逆 path 制限の引き戻し錐。
方針：指定 path と lax pullback への比較射を脚に取る。
規約：元の path の包含の等式を可換性とする。
使われ方：通常の引き戻しの全部分圏への比較の基礎。 -/
def catPullbackLaxCone (p : A ⟶ C) (q : B ⟶ C) :
    PullbackCone (equivalencePathι C) (laxPullbackArrow p q) :=
  PullbackCone.mk (catPullbackPath p q) (catPullbackToLax p q)
    (catPullbackToLax_arrow p q).symm

/-- 概要：可逆 path と lax pullback の適合した族を元の候補へ持ち上げる。
方針：lax pullback の二射影と元の可逆 path を使う。
規約：全ての単体集合パラメータを扱う。
使われ方：可逆 path 制限の厳密な引き戻しの普遍性。 -/
def catPullbackLaxConeLift (p : A ⟶ C) (q : B ⟶ C)
    (s : PullbackCone (equivalencePathι C) (laxPullbackArrow p q)) :
    s.pt ⟶ catPullback p q :=
  catPullbackLift p q (s.snd ≫ laxPullbackFst p q)
    (s.snd ≫ laxPullbackSnd p q) s.fst
    (by rw [equivalencePathEndpoint, ← Category.assoc, s.condition,
          Category.assoc, laxPullbackArrow_source, Category.assoc])
    (by rw [equivalencePathEndpoint, ← Category.assoc, s.condition,
          Category.assoc, laxPullbackArrow_target, Category.assoc])

/-- 概要：可逆 path 制限の候補錐は厳密な極限錐。
方針：三成分の lift と二射影・指定 path の外延性を使う。
規約：Cat_∞ の極限とは区別した単体集合内の極限。
使われ方：同値矢印による lax pullback の制限。 -/
def catPullbackLaxCone_isLimit (p : A ⟶ C) (q : B ⟶ C) :
    IsLimit (catPullbackLaxCone p q) := by
  apply PullbackCone.IsLimit.mk _ (catPullbackLaxConeLift p q)
  · intro s
    exact catPullbackLift_path ..
  · intro s
    apply laxPullback_hom_ext p q
    · rw [Category.assoc, catPullbackToLax_arrow, ← Category.assoc]
      exact (congrArg (fun f ↦ f ≫ equivalencePathι C)
        (catPullbackLift_path ..)).trans s.condition
    · rw [Category.assoc, catPullbackToLax_fst]
      exact catPullbackLift_fst ..
    · rw [Category.assoc, catPullbackToLax_snd]
      exact catPullbackLift_snd ..
  · intro s m hpath hlax
    apply catPullback_hom_ext p q
    · have hf : m ≫ catPullbackFst p q = s.snd ≫ laxPullbackFst p q := by
        rw [← catPullbackToLax_fst, ← Category.assoc]
        exact congrArg (fun f ↦ f ≫ laxPullbackFst p q) hlax
      exact hf.trans (catPullbackLift_fst ..).symm
    · have hs : m ≫ catPullbackSnd p q = s.snd ≫ laxPullbackSnd p q := by
        rw [← catPullbackToLax_snd, ← Category.assoc]
        exact congrArg (fun f ↦ f ≫ laxPullbackSnd p q) hlax
      exact hs.trans (catPullbackLift_snd ..).symm
    · exact hpath.trans (catPullbackLift_path ..).symm

/-- 概要：指定 path と比較射の正方形は引き戻し。
方針：元の候補錐の厳密な極限性を使う。
規約：頂点は元の catPullback p q そのもの。
使われ方：Tamme §1 Remark 7 の可逆 path に沿う制限。 -/
lemma catPullbackToLax_isPullback (p : A ⟶ C) (q : B ⟶ C) :
    IsPullback (catPullbackPath p q) (catPullbackToLax p q)
      (equivalencePathι C) (laxPullbackArrow p q) :=
  IsPullback.of_isLimit (catPullbackLaxCone_isLimit p q)

end SerrePositivity.InfinityCategories.F2
