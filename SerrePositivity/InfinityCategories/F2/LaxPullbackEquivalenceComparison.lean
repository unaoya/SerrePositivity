module

public import SerrePositivity.InfinityCategories.F2.CatPullbackToLax

/-!
概要：通常の引き戻し候補と同値矢印の全部分複体との比較射。
方針：三成分の厳密な lift を両方向に構成する。
規約：元の二射影と指定可逆 path を保つ。
使われ方：Tamme §1 Remark 7 の比較同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}}

/-- 概要：通常の引き戻し候補から同値矢印の全部分複体への射。
方針：比較射の全頂点が同値条件を満たすことを使う。
規約：全部分複体への制限だけを行う。
使われ方：比較同型の順射。 -/
def catPullbackToEquivalenceSubcomplex (p : A ⟶ C) (q : B ⟶ C) :
    catPullback p q ⟶ (laxPullbackEquivalenceSubcomplex p q : SSet.{u}) :=
  fullSubcomplexLift (IsLaxEquivalenceVertex p q) (catPullbackToLax p q)
    (catPullbackToLax_vertex p q)

/-- 概要：全部分複体への比較射の包含は元の比較射。
方針：全部分複体への lift の包含を計算する。
規約：射の厳密な等式。
使われ方：元の lax pullback の三成分との照合。 -/
lemma catPullbackToEquivalenceSubcomplex_ι (p : A ⟶ C) (q : B ⟶ C) :
    catPullbackToEquivalenceSubcomplex p q ≫ (laxPullbackEquivalenceSubcomplex p q).ι =
      catPullbackToLax p q := rfl

/-- 概要：同値矢印の全部分複体から通常の引き戻し候補への射。
方針：二射影と元の可逆 path から厳密な lift を作る。
規約：元の path の両端条件を矢印射影から得る。
使われ方：比較同型の逆射。 -/
def equivalenceSubcomplexToCatPullback (p : A ⟶ C) (q : B ⟶ C) :
    (laxPullbackEquivalenceSubcomplex p q : SSet.{u}) ⟶ catPullback p q :=
  catPullbackLift p q
    ((laxPullbackEquivalenceSubcomplex p q).ι ≫ laxPullbackFst p q)
    ((laxPullbackEquivalenceSubcomplex p q).ι ≫ laxPullbackSnd p q)
    (laxPullbackEquivalencePath p q)
    (by rw [equivalencePathEndpoint, ← Category.assoc, laxPullbackEquivalencePath_ι,
          Category.assoc, laxPullbackArrow_source, Category.assoc])
    (by rw [equivalencePathEndpoint, ← Category.assoc, laxPullbackEquivalencePath_ι,
          Category.assoc, laxPullbackArrow_target, Category.assoc])

/-- 概要：逆向き比較射は第一射影を保つ。
方針：通常の引き戻しへの lift の射影を計算する。
規約：包含後の元の A への射。
使われ方：比較の往復条件と射影の保持。 -/
lemma equivalenceSubcomplexToCatPullback_fst (p : A ⟶ C) (q : B ⟶ C) :
    equivalenceSubcomplexToCatPullback p q ≫ catPullbackFst p q =
      (laxPullbackEquivalenceSubcomplex p q).ι ≫ laxPullbackFst p q :=
  catPullbackLift_fst ..

/-- 概要：逆向き比較射は第二射影を保つ。
方針：通常の引き戻しへの lift の射影を計算する。
規約：包含後の元の B への射。
使われ方：比較の往復条件と射影の保持。 -/
lemma equivalenceSubcomplexToCatPullback_snd (p : A ⟶ C) (q : B ⟶ C) :
    equivalenceSubcomplexToCatPullback p q ≫ catPullbackSnd p q =
      (laxPullbackEquivalenceSubcomplex p q).ι ≫ laxPullbackSnd p q :=
  catPullbackLift_snd ..

/-- 概要：逆向き比較射は元の指定可逆 path を保つ。
方針：通常の引き戻しへの lift の path 成分を計算する。
規約：全パラメータの path の等式。
使われ方：指定 path の保持と比較の往復条件。 -/
lemma equivalenceSubcomplexToCatPullback_path (p : A ⟶ C) (q : B ⟶ C) :
    equivalenceSubcomplexToCatPullback p q ≫ catPullbackPath p q =
      laxPullbackEquivalencePath p q := catPullbackLift_path ..

end SerrePositivity.InfinityCategories.F2
