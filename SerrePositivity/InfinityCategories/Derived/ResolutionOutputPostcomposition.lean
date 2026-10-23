module
public import SerrePositivity.InfinityCategories.Derived.ResolutionComparisonPrecompIdentity
public import SerrePositivity.InfinityCategories.Derived.ResolutionSourceComparisonNormalization
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoTransportAlgebra
/-!
概要：元の指定出力比較を、同じ出力関手による後合成と厳密に照合する。
方針：指定入力比較を保ち、後合成の合成則と出力射影の等式だけを移送する。
規約：同値の逆も比較も選び直さない。使われ方：出力宇宙の上げ下げの回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
lemma qCatResolutionOutputPrecompIso_postcomp_heq
    {X Y A B T V : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    [Quasicategory A] [Quasicategory B] [Quasicategory T] [Quasicategory V]
    (Q : QCatEquivalence X A) (S : QCatEquivalence Y B)
    (h : A ⟶ B) (H : X ⟶ Y) (RX : X ⟶ T) (RY : Y ⟶ T)
    (hs : H ≫ S.hom = Q.hom ≫ h) (hr : H ≫ RY = RX) (L : T ⟶ V) :
    HEq ((qCatResolutionOutputPrecompIso Q S h H RX RY hs hr).postcomp L)
      (qCatResolutionOutputPrecompIso Q S h H (RX ≫ L) (RY ≫ L) hs
        (by rw [← Category.assoc, hr])) := by
  let d := qCatResolutionSourceComparisonIso Q S h H hs
  have ha := qCatResolutionOutputPrecompIso_sourceComparison_heq Q S h H RX RY hs hr
  have hf : (Q.inv ≫ H) ≫ RY = Q.inv ≫ RX := by rw [Category.assoc, hr]
  have hg : (h ≫ S.inv) ≫ RY = h ≫ S.inv ≫ RY := Category.assoc _ _ _
  have hp := F2.functorIso_postcomp_heq_of_heq (d.postcomp RY)
    (qCatResolutionOutputPrecompIso Q S h H RX RY hs hr) hf hg ha L
  have hb := qCatResolutionOutputPrecompIso_sourceComparison_heq Q S h H
    (RX ≫ L) (RY ≫ L) hs (by rw [← Category.assoc, hr])
  exact hp.trans ((heq_of_eq (F2.functorIso_postcomp_postcomp d RY L)).trans hb.symm)
lemma qCatResolutionOutputComparisonIso_postcomp_heq
    {X Y A T V : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    [Quasicategory A] [Quasicategory T] [Quasicategory V]
    (Q : QCatEquivalence X A) (S : QCatEquivalence Y A)
    (H : X ⟶ Y) (RX : X ⟶ T) (RY : Y ⟶ T)
    (hs : H ≫ S.hom = Q.hom) (hr : H ≫ RY = RX) (L : T ⟶ V) :
    HEq ((qCatResolutionOutputComparisonIso Q S H RX RY hs hr).postcomp L)
      (qCatResolutionOutputComparisonIso Q S H (RX ≫ L) (RY ≫ L) hs
        (by rw [← Category.assoc, hr])) := by
  have hs' : H ≫ S.hom = Q.hom ≫ 𝟙 A := by simpa only [Category.comp_id] using hs
  have hp := F2.functorIso_postcomp_heq_of_heq
    (qCatResolutionOutputPrecompIso Q S (𝟙 A) H RX RY hs' hr)
    (qCatResolutionOutputComparisonIso Q S H RX RY hs hr) rfl rfl
    (qCatResolutionOutputComparisonIso_precomp_id_heq Q S H RX RY hs hr) L
  have hq := qCatResolutionOutputPrecompIso_postcomp_heq Q S (𝟙 A) H RX RY hs' hr L
  have ht := qCatResolutionOutputComparisonIso_precomp_id_heq Q S H
    (RX ≫ L) (RY ≫ L) hs (by rw [← Category.assoc, hr])
  exact hp.trans (hq.trans ht.symm)
end SerrePositivity.InfinityCategories
