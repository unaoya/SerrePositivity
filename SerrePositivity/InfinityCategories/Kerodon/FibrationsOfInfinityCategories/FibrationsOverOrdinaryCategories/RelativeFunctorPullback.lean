module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorComposition

/-!
概要：底の射に沿う引き戻しは相対写像空間全体に作用する。
方針：引き戻した始域の第一射影で評価し、標的の引き戻しへ持ち上げる。
規約：通常の単体集合の引き戻しを用い、fibration 性を要求しない。
使われ方：Kerodon §5.3.1（Tag 035D）、left fibrations の豊穣的な底変換の Hom への作用。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：二つの底上の対象を同時に引き戻す相対写像空間の射。
方針：元の相対評価と引き戻しの底への射影を組にして curry する。
規約：始域と標的を同じ底の射 k に沿って引き戻す。
使われ方：Kerodon §5.3.1（Tag 035D）、分類の fibration 側の底変換。 -/
noncomputable def relativeFunctorPullback {E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (k : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (pullback.snd q k) (pullback.snd p k) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry
    (pullback.lift
      ((pullback.fst p k ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (𝟙 _))
      (fst (pullback p k) _ ≫ pullback.snd p k) (by
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection, ← Category.assoc,
          whiskerRight_fst, Category.assoc, pullback.condition, ← Category.assoc]))
    (pullback.lift_snd _ _ _)

/-- 概要：引き戻した写像族の第一射影は元の写像族の制限。
方針：相対 uncurry の自然性と引き戻しの第一射影を計算する。
規約：任意の単体集合 T をパラメーターとして扱う。
使われ方：Kerodon §5.3.1（Tag 035D）、底変換が高次の写像族にも作用することの計算則。 -/
lemma relativeFunctorPullback_uncurry_fst {E F B D T : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (k : D ⟶ B)
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (f ≫ relativeFunctorPullback p q k) ≫ pullback.fst q k =
      (pullback.fst p k ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry f := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorUncurry_naturality, relativeFunctorPullback,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry, Category.assoc, pullback.lift_fst]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorUncurry_naturality (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p)) f
  rw [Category.comp_id] at h
  rw [h, ← Category.assoc, ← Category.assoc]
  congr 1

/-- 概要：引き戻した写像族の第二射影は始域の底への射影。
方針：相対 uncurry の底を保つ式を適用する。
規約：パラメーター依存を第一射影で忘れる。
使われ方：Kerodon §5.3.1（Tag 035D）、底変換の二射影による等式判定。 -/
lemma relativeFunctorPullback_uncurry_snd {E F B D T : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (k : D ⟶ B)
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (f ≫ relativeFunctorPullback p q k) ≫ pullback.snd q k =
      fst (pullback p k) T ≫ pullback.snd p k :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
