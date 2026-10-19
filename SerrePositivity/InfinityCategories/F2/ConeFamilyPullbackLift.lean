module

public import SerrePositivity.InfinityCategories.F2.ConeFamilyPullbackMaps
public import SerrePositivity.InfinityCategories.F2.InternalHomPullbackLift

/-!
概要：成分ごとの錐族の適合した全パラメータの族を引き戻しの錐族へ合わせる。
方針：内部 Hom の lift を作り、元の図式の固定条件を二射影で照合する。
規約：図式と錐の全単体を厳密に保持する。
使われ方：錐族と引き戻しの交換の普遍性。
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

/-- 概要：適合した二成分の錐族から全錐の内部 Hom の族を作る。
方針：包含後の可換性から内部 Hom の引き戻し lift を使う。
規約：この射の段階では図式の固定条件を忘れている。
使われ方：錐族への lift の構成と成分計算。 -/
def coneFamilyPullbackRawLift : T ⟶ (ihom (join (Δ[0] : SSet.{u}) J)).obj (pullback p q) :=
  internalHomPullbackLift p q
    (a ≫ vertexFiberι (coneRestriction J E) (functorVertex (r ≫ pullback.fst p q)))
    (b ≫ vertexFiberι (coneRestriction J D) (functorVertex (r ≫ pullback.snd p q))) (by
      have hh := congrArg (fun f ↦ f ≫ vertexFiberι (coneRestriction J B)
        (functorVertex ((r ≫ pullback.fst p q) ≫ p))) h
      simpa only [Category.assoc, coneFamilyPostcomp_ι,
        coneFamilyPullbackBaseMap_ι] using hh)

/-- 概要：構成した全錐の族は元の図式に制限される。
方針：内部 Hom の引き戻しへの射の二射影を計算し、各成分の図式固定条件を使う。
規約：全てのパラメータ単体で同じ元の図式を保つ。
使われ方：全錐の族を元の図式の錐族へ戻す。 -/
lemma coneFamilyPullbackRawLift_restriction :
    coneFamilyPullbackRawLift p q r a b h ≫ coneRestriction J (pullback p q) =
      SSet.const (functorVertex r) := by
  apply internalHomPullback_hom_ext p q
  · change (_ ≫ (pre (joinInr (Δ[0] : SSet.{u}) J)).app (pullback p q)) ≫
      (ihom J).map (pullback.fst p q) = _
    rw [Category.assoc, ← (pre (joinInr (Δ[0] : SSet.{u}) J)).naturality
        (pullback.fst p q), ← Category.assoc]
    change (internalHomPullbackLift p q _ _ _ ≫ _) ≫ _ = _
    rw [internalHomPullbackLift_fst]
    change (a ≫ vertexFiberι (coneRestriction J E) _) ≫ coneRestriction J E = _
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.const_comp]
    rfl
  · change (_ ≫ (pre (joinInr (Δ[0] : SSet.{u}) J)).app (pullback p q)) ≫
      (ihom J).map (pullback.snd p q) = _
    rw [Category.assoc, ← (pre (joinInr (Δ[0] : SSet.{u}) J)).naturality
        (pullback.snd p q), ← Category.assoc]
    change (internalHomPullbackLift p q _ _ _ ≫ _) ≫ _ = _
    rw [internalHomPullbackLift_snd]
    change (b ≫ vertexFiberι (coneRestriction J D) _) ≫ coneRestriction J D = _
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.const_comp]
    rfl

/-- 概要：適合した二成分の錐族を元の引き戻しの錐族へ合わせる。
方針：全錐の族と図式の制限の等式を fiber の lift に渡す。
規約：始域 T は任意の単体集合。
使われ方：錐族の引き戻しの極限性。 -/
def coneFamilyPullbackLift : T ⟶ coneFamily r :=
  vertexFiberLift (coneRestriction J (pullback p q)) (functorVertex r)
    (coneFamilyPullbackRawLift p q r a b h) (coneFamilyPullbackRawLift_restriction p q r a b h)

end SerrePositivity.InfinityCategories.F2
