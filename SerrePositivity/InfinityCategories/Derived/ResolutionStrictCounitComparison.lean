module
public import SerrePositivity.InfinityCategories.Derived.ResolutionCounitComparison
public import SerrePositivity.InfinityCategories.Derived.ResolutionSourceComparisonNormalization
/-!
概要：厳密切断の指定入力比較を、基底上の指定恒等同型へ正規化する。
方針：指定された同じ比較と端点等式を保って全関手射を比較する。
規約：元の指定同型を変更しない。使われ方：実 augmentation と入力比較の正方形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
/-- 厳密な単位関係の二余単位の指定比較は、同じ基底射の恒等同型に一致する。 -/
lemma resolutionCounitComparison_strict_heq {A B : SSet.{u}} {f : A ⟶ A} {g : B ⟶ B}
    (hf : f = 𝟙 A) (hg : g = 𝟙 B) (h : A ⟶ B) :
    HEq (resolutionCounitComparison
      (eqToIso (congrArg (fun m => HomotopyCategory.mk (functorVertex m)) hf))
      (eqToIso (congrArg (fun m => HomotopyCategory.mk (functorVertex m)) hg)) h)
      (Iso.refl (HomotopyCategory.mk (functorVertex h))) := by
  subst f g
  simp only [eqToIso_refl, resolutionCounitComparison, F2.functorIso_postcomp_eq_mapIso,
    F2.functorIso_precomp_eq_mapIso, CategoryTheory.Functor.mapIso_refl]
  rfl
/-- 厳密切断の指定余単位を使う入力比較は、基底への後合成で恒等同型に一致する。 -/
lemma qCatResolutionSourceComparisonIso_strict_postcomp_heq
    {X Y A B : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    [Quasicategory A] [Quasicategory B]
    (Q : QCatEquivalence X A) (S : QCatEquivalence Y B)
    (h : A ⟶ B) (H : X ⟶ Y) (hs : H ≫ S.hom = Q.hom ≫ h)
    (hq : Q.inv ≫ Q.hom = 𝟙 A) (hs₀ : S.inv ≫ S.hom = 𝟙 B)
    (hQ : Q.invHomIso = eqToIso
      (congrArg (fun m => HomotopyCategory.mk (functorVertex m)) hq))
    (hS : S.invHomIso = eqToIso
      (congrArg (fun m => HomotopyCategory.mk (functorVertex m)) hs₀)) :
    HEq ((qCatResolutionSourceComparisonIso Q S h H hs).postcomp S.hom)
      (Iso.refl (HomotopyCategory.mk (functorVertex h))) := by
  rw [qCatResolutionSourceComparisonIso_postcomp]
  have hb := qCatResolutionBaseComparisonIso_heq Q S h H hs
  have hc := resolutionCounitComparison_strict_heq hq hs₀ h
  rw [← hQ, ← hS] at hc
  exact hb.trans hc
end SerrePositivity.InfinityCategories
