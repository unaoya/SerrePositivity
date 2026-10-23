module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeFamilyPullbackLift

/-!
概要：錐族の引き戻し lift の両成分と射の一意性。
方針：fiber の包含後に内部 Hom の引き戻しの成分を計算する。
規約：元の図式の厳密な固定条件を保持する。
使われ方：錐族の引き戻し正方形の普遍性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {J E D B T : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B) (r : J ⟶ pullback p q)
variable (a : T ⟶ coneFamily (r ≫ pullback.fst p q))
variable (b : T ⟶ coneFamily (r ≫ pullback.snd p q))
variable (h : a ≫ coneFamilyPostcomp (r ≫ pullback.fst p q) p =
  b ≫ coneFamilyPullbackBaseMap p q r)

/-- 概要：錐族の lift を含めると構成した全錐の族。
方針：頂点 fiber への lift の包含を計算する。
規約：全次数での族の等式。
使われ方：二射影の計算の共通部分。 -/
lemma coneFamilyPullbackLift_ι : coneFamilyPullbackLift p q r a b h ≫
    vertexFiberι (coneRestriction J (pullback p q)) (functorVertex r) =
      coneFamilyPullbackRawLift p q r a b h := rfl

/-- 概要：錐族の lift の第一成分は指定された第一の族。
方針：包含後に内部 Hom の lift の第一成分を計算する。
規約：図式固定の錐族内の厳密な等式。
使われ方：錐族の引き戻しの第一射影。 -/
lemma coneFamilyPullbackLift_fst :
    coneFamilyPullbackLift p q r a b h ≫ coneFamilyPostcomp r (pullback.fst p q) = a := by
  apply vertexFiber_hom_ext (coneRestriction J E) (functorVertex (r ≫ pullback.fst p q))
  rw [Category.assoc, coneFamilyPostcomp_ι, ← Category.assoc, coneFamilyPullbackLift_ι]
  exact internalHomPullbackLift_fst ..

/-- 概要：錐族の lift の第二成分は指定された第二の族。
方針：包含後に内部 Hom の lift の第二成分を計算する。
規約：図式固定の錐族内の厳密な等式。
使われ方：錐族の引き戻しの第二射影。 -/
lemma coneFamilyPullbackLift_snd :
    coneFamilyPullbackLift p q r a b h ≫ coneFamilyPostcomp r (pullback.snd p q) = b := by
  apply vertexFiber_hom_ext (coneRestriction J D) (functorVertex (r ≫ pullback.snd p q))
  rw [Category.assoc, coneFamilyPostcomp_ι, ← Category.assoc, coneFamilyPullbackLift_ι]
  exact internalHomPullbackLift_snd ..

/-- 概要：引き戻しの錐族への射は二つの成分で決まる。
方針：包含後に内部 Hom の引き戻しへの射の外延性を使う。
規約：始域のパラメータは任意。
使われ方：錐族の普遍性の一意性。 -/
lemma coneFamilyPullback_hom_ext {f g : T ⟶ coneFamily r}
    (he : f ≫ coneFamilyPostcomp r (pullback.fst p q) =
      g ≫ coneFamilyPostcomp r (pullback.fst p q))
    (hd : f ≫ coneFamilyPostcomp r (pullback.snd p q) =
      g ≫ coneFamilyPostcomp r (pullback.snd p q)) : f = g := by
  apply vertexFiber_hom_ext (coneRestriction J (pullback p q)) (functorVertex r)
  apply internalHomPullback_hom_ext p q
  · simpa only [Category.assoc, coneFamilyPostcomp_ι] using
      congrArg (fun f ↦ f ≫ vertexFiberι (coneRestriction J E)
        (functorVertex (r ≫ pullback.fst p q))) he
  · simpa only [Category.assoc, coneFamilyPostcomp_ι] using
      congrArg (fun f ↦ f ≫ vertexFiberι (coneRestriction J D)
        (functorVertex (r ≫ pullback.snd p q))) hd

end SerrePositivity.InfinityCategories.F2
