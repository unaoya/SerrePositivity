module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPostcomposition
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：同じ底上の全空間の引き戻しは、全相対関手空間でも引き戻し。
方針：curry の普遍性で任意のパラメーターの族を全空間の引き戻しへ持ち上げる。
規約：充填性を要求せず、元の底の全図式を保持する。
使われ方：left fibrations の引き戻しを全豊穣 Hom で極限と判定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 概要：後合成自体の展開は元の全評価への後合成。
方針：恒等族について後合成の展開則を使う。
規約：元の固定図式を保つ。
使われ方：相対関手空間の射影の合成計算。 -/
lemma relativeFunctorUncurry_post_identity {A E F X : SSet.{u}}
    (e : E ⟶ X) (f : F ⟶ X) (p : E ⟶ F) (hp : p ≫ f = e) (a : A ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost e f p hp a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace e a)) ≫ p := by
  simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_post e f p hp a (𝟙 _)

variable {A E D B X : SSet.{u}}
  (p : E ⟶ B) (q : D ⟶ B) (e : E ⟶ X) (d : D ⟶ X) (b : B ⟶ X)
  (hp : p ≫ b = e) (hq : q ≫ b = d) (a : A ⟶ X)

include hp hq

/-- 概要：第二射影も元の底への射影を保つ。
方針：二つの底の可換条件と引き戻しの可換条件を合わせる。
規約：引き戻しの底への射影は第一射影との合成とする。
使われ方：相対関手の第二射影。 -/
lemma relativePullback_snd_over :
    pullback.snd p q ≫ d = pullback.fst p q ≫ e := by
  rw [← hp, ← hq, ← Category.assoc, ← Category.assoc, pullback.condition]

/-- 概要：相対関手空間の両後合成は元の底上で可換。
方針：全パラメーターの uncurry の単射性と引き戻しの可換条件を使う。
規約：元の全図式 a を固定する。
使われ方：相対関手空間の引き戻し錐。 -/
lemma relativeFunctorPullback_condition :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost (pullback.fst p q ≫ e) e (pullback.fst p q) rfl a ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost e b p hp a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost (pullback.fst p q ≫ e) d (pullback.snd p q)
        (relativePullback_snd_over p q e d b hp hq) a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost d b q hq a := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective b a
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_post, relativeFunctorUncurry_post_identity,
    Category.assoc, pullback.condition]

/-- 概要：元の引き戻しの相対関手空間を頂点とする指定錐。
方針：両射影による後合成を両脚とする。
規約：元の引き戻しと元の全空間への射影を固定する。
使われ方：全豊穣 Hom の strict な引き戻し。 -/
def relativeFunctorPullbackCone : PullbackCone
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost e b p hp a) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost d b q hq a) :=
  PullbackCone.mk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost (pullback.fst p q ≫ e) e (pullback.fst p q) rfl a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost (pullback.fst p q ≫ e) d (pullback.snd p q)
      (relativePullback_snd_over p q e d b hp hq) a)
    (relativeFunctorPullback_condition p q e d b hp hq a)

/-- 概要：可換な全相対関手の二族は元の引き戻しへ一意に貼れる。
方針：両族を展開して引き戻しへ持ち上げ、元の底上で curry する。
規約：任意のパラメーター空間を扱う。
使われ方：相対関手空間の引き戻し錐の普遍射。 -/
def relativeFunctorPullbackConeLift (s : PullbackCone
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost e b p hp a) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost d b q hq a)) :
    s.pt ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (pullback.fst p q ≫ e) a := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry s.fst ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry s.snd ≫ q := by
    have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (p := b) (a := a)) s.condition
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_post] using h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry (pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry s.fst)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry s.snd) h) (by
      rw [← Category.assoc, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection])

/-- 概要：全相対関手空間は同じ底上の全空間の引き戻しを保つ。
方針：任意の二族を curry で貼り、両射影による一意性を使う。
規約：Kan 性や fibration 性を追加しない。
使われ方：coherent nerve 内の引き戻しの豊穣極限判定。 -/
def relativeFunctorPullbackCone_isLimit :
    IsLimit (relativeFunctorPullbackCone p q e d b hp hq a) := by
  apply PullbackCone.IsLimit.mk _ (relativeFunctorPullbackConeLift p q e d b hp hq a)
  · intro s
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective e a
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_post, relativeFunctorPullbackConeLift,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry, pullback.lift_fst]
  · intro s
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective d a
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_post, relativeFunctorPullbackConeLift,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry, pullback.lift_snd]
  · intro s m hm₁ hm₂
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective (pullback.fst p q ≫ e) a
    apply pullback.hom_ext
    · have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (p := e) (a := a)) hm₁
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_post, relativeFunctorPullbackConeLift,
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry, pullback.lift_fst] using h
    · have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (p := d) (a := a)) hm₂
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_post, relativeFunctorPullbackConeLift,
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry, pullback.lift_snd] using h

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
