module
public import SerrePositivity.InfinityCategories.Derived.ResolutionOutputPostcomposition
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
lemma qCatResolutionOutputPrecompIso_postcomp_heq_of_outputs
    {X Y A B T V : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    [Quasicategory A] [Quasicategory B] [Quasicategory T] [Quasicategory V]
    (Q : QCatEquivalence X A) (S : QCatEquivalence Y B)
    (h : A ⟶ B) (H : X ⟶ Y) (RX : X ⟶ T) (RY : Y ⟶ T)
    (RX' : X ⟶ V) (RY' : Y ⟶ V)
    (hs : H ≫ S.hom = Q.hom ≫ h) (hr : H ≫ RY = RX) (hr' : H ≫ RY' = RX')
    (L : T ⟶ V) (hx : RX ≫ L = RX') (hy : RY ≫ L = RY') :
    HEq ((qCatResolutionOutputPrecompIso Q S h H RX RY hs hr).postcomp L)
      (qCatResolutionOutputPrecompIso Q S h H RX' RY' hs hr') := by
  cases hx
  cases hy
  exact qCatResolutionOutputPrecompIso_postcomp_heq Q S h H RX RY hs hr L
lemma qCatResolutionOutputComparisonIso_postcomp_heq_of_outputs
    {X Y A T V : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    [Quasicategory A] [Quasicategory T] [Quasicategory V]
    (Q : QCatEquivalence X A) (S : QCatEquivalence Y A)
    (H : X ⟶ Y) (RX : X ⟶ T) (RY : Y ⟶ T)
    (RX' : X ⟶ V) (RY' : Y ⟶ V)
    (hs : H ≫ S.hom = Q.hom) (hr : H ≫ RY = RX) (hr' : H ≫ RY' = RX')
    (L : T ⟶ V) (hx : RX ≫ L = RX') (hy : RY ≫ L = RY') :
    HEq ((qCatResolutionOutputComparisonIso Q S H RX RY hs hr).postcomp L)
      (qCatResolutionOutputComparisonIso Q S H RX' RY' hs hr') := by
  cases hx
  cases hy
  exact qCatResolutionOutputComparisonIso_postcomp_heq Q S H RX RY hs hr L
end SerrePositivity.InfinityCategories
