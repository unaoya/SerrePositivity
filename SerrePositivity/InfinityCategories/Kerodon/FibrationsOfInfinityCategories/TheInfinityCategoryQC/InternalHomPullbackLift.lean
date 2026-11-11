module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamily
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：内部 Hom の引き戻し保存による指定成分の lift。
方針：右随伴の引き戻し保存の同型の逆で二成分を合わせる。
規約：試験対象とパラメータは任意の単体集合。
使われ方：錐族の引き戻し比較の全パラメータの構成。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：二つの指定内部 Hom 成分を引き戻しの内部 Hom に合わせる。
方針：引き戻し保存同型の逆を通常の lift に合成する。
規約：成分の可換性は射の等式として与える。
使われ方：錐族の全パラメータの lift。 -/
def internalHomPullbackLift {K T E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    (a : T ⟶ (ihom K).obj E) (b : T ⟶ (ihom K).obj D)
    (h : a ≫ (ihom K).map p = b ≫ (ihom K).map q) :
    T ⟶ (ihom K).obj (pullback p q) :=
  pullback.lift a b h ≫ (PreservesPullback.iso (ihom K) p q).inv

/-- 概要：内部 Hom の lift の第一成分は指定された第一成分。
方針：引き戻し保存同型の逆の第一射影を計算する。
規約：実際の射の等式。
使われ方：錐族の第一成分の保持。 -/
lemma internalHomPullbackLift_fst {K T E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    (a : T ⟶ (ihom K).obj E) (b : T ⟶ (ihom K).obj D) (h) :
    internalHomPullbackLift p q a b h ≫ (ihom K).map (pullback.fst p q) = a := by
  rw [internalHomPullbackLift, Category.assoc, PreservesPullback.iso_inv_fst, pullback.lift_fst]

/-- 概要：内部 Hom の lift の第二成分は指定された第二成分。
方針：引き戻し保存同型の逆の第二射影を計算する。
規約：実際の射の等式。
使われ方：錐族の第二成分の保持。 -/
lemma internalHomPullbackLift_snd {K T E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    (a : T ⟶ (ihom K).obj E) (b : T ⟶ (ihom K).obj D) (h) :
    internalHomPullbackLift p q a b h ≫ (ihom K).map (pullback.snd p q) = b := by
  rw [internalHomPullbackLift, Category.assoc, PreservesPullback.iso_inv_snd, pullback.lift_snd]

/-- 概要：引き戻しの内部 Hom への射は二成分で決まる。
方針：uncurry の単射性と引き戻しの外延性を使う。
規約：図式固定や quasicategory 性は仮定しない。
使われ方：錐族の lift の図式制限と一意性。 -/
lemma internalHomPullback_hom_ext {K T E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    {a b : T ⟶ (ihom K).obj (pullback p q)}
    (h₁ : a ≫ (ihom K).map (pullback.fst p q) = b ≫ (ihom K).map (pullback.fst p q))
    (h₂ : a ≫ (ihom K).map (pullback.snd p q) = b ≫ (ihom K).map (pullback.snd p q)) :
    a = b := by
  apply uncurry_injective
  apply pullback.hom_ext
  · simpa only [uncurry_natural_right] using congrArg uncurry h₁
  · simpa only [uncurry_natural_right] using congrArg uncurry h₂

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
