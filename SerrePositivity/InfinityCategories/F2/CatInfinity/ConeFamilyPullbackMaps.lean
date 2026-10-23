module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeFamilyPostcompOfEq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：引き戻し内の図式の錐族から各成分の錐族への射。
方針：二射影による後合成と元の引き戻しの可換条件を使う。
規約：共通の底の図式は第一成分の像に固定する。
使われ方：錐族と引き戻しの交換の正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {J E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B) (r : J ⟶ pullback p q)

/-- 概要：第二成分の錐族を第一成分の像の錐族へ写す。
方針：第二関手で後合成し、引き戻しの可換条件で底の図式を固定する。
規約：底の図式は (r≫fst)≫p。
使われ方：錐族の引き戻し正方形の第二の脚。 -/
def coneFamilyPullbackBaseMap :
    coneFamily (r ≫ pullback.snd p q) ⟶ coneFamily ((r ≫ pullback.fst p q) ≫ p) :=
  coneFamilyPostcompOfEq (r ≫ pullback.snd p q) q (by
    rw [Category.assoc, Category.assoc, pullback.condition])

/-- 概要：第二の脚を含めると元の内部 Hom の後合成になる。
方針：図式の等式で固定した後合成の包含を計算する。
規約：全次数の族の等式。
使われ方：錐族の正方形の可換性と lift。 -/
lemma coneFamilyPullbackBaseMap_ι :
    coneFamilyPullbackBaseMap p q r ≫
      vertexFiberι (coneRestriction J B) (functorVertex ((r ≫ pullback.fst p q) ≫ p)) =
    vertexFiberι (coneRestriction J D) (functorVertex (r ≫ pullback.snd p q)) ≫
      (ihom (join (Δ[0] : SSet.{u}) J)).map q := coneFamilyPostcompOfEq_ι ..

/-- 概要：錐族の二射影は共通の底の上で可換。
方針：包含後に内部 Hom の後合成へ戻し、元の引き戻しの可換性を使う。
規約：二つの底の図式は指定された同じ射として扱う。
使われ方：錐族の引き戻し比較射の構成。 -/
lemma coneFamilyPullback_condition :
    coneFamilyPostcomp r (pullback.fst p q) ≫ coneFamilyPostcomp (r ≫ pullback.fst p q) p =
      coneFamilyPostcomp r (pullback.snd p q) ≫ coneFamilyPullbackBaseMap p q r := by
  apply vertexFiber_hom_ext (coneRestriction J B)
    (functorVertex ((r ≫ pullback.fst p q) ≫ p))
  calc
    _ = vertexFiberι (coneRestriction J (pullback p q)) (functorVertex r) ≫
        (ihom (join (Δ[0] : SSet.{u}) J)).map (pullback.fst p q) ≫
        (ihom (join (Δ[0] : SSet.{u}) J)).map p := by
      rw [Category.assoc, coneFamilyPostcomp_ι, ← Category.assoc,
        coneFamilyPostcomp_ι, Category.assoc]
    _ = vertexFiberι (coneRestriction J (pullback p q)) (functorVertex r) ≫
        (ihom (join (Δ[0] : SSet.{u}) J)).map (pullback.snd p q) ≫
        (ihom (join (Δ[0] : SSet.{u}) J)).map q := by
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
        pullback.condition]
    _ = _ := by
      symm
      rw [Category.assoc, coneFamilyPullbackBaseMap_ι, ← Category.assoc,
        coneFamilyPostcomp_ι, Category.assoc]

end SerrePositivity.InfinityCategories.F2
