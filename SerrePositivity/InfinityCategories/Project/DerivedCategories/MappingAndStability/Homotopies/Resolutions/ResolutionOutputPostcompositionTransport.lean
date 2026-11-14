module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.ResolutionOutputPostcomposition
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
lemma qCatResolutionOutputPrecompIso_postcomp_heq_of_outputs
    {X Y A B T V : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    [Quasicategory A] [Quasicategory B] [Quasicategory T] [Quasicategory V]
    (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X A) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y B)
    (h : A ⟶ B) (H : X ⟶ Y) (RX : X ⟶ T) (RY : Y ⟶ T)
    (RX' : X ⟶ V) (RY' : Y ⟶ V)
    (hs : H ≫ S.hom = Q.hom ≫ h) (hr : H ≫ RY = RX) (hr' : H ≫ RY' = RX')
    (L : T ⟶ V) (hx : RX ≫ L = RX') (hy : RY ≫ L = RY') :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso Q S h H RX RY hs hr).postcomp L)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso Q S h H RX' RY' hs hr') := by
  cases hx
  cases hy
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso_postcomp_heq Q S h H RX RY hs hr L
lemma qCatResolutionOutputComparisonIso_postcomp_heq_of_outputs
    {X Y A T V : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    [Quasicategory A] [Quasicategory T] [Quasicategory V]
    (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X A) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y A)
    (H : X ⟶ Y) (RX : X ⟶ T) (RY : Y ⟶ T)
    (RX' : X ⟶ V) (RY' : Y ⟶ V)
    (hs : H ≫ S.hom = Q.hom) (hr : H ≫ RY = RX) (hr' : H ≫ RY' = RX')
    (L : T ⟶ V) (hx : RX ≫ L = RX') (hy : RY ≫ L = RY') :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputComparisonIso Q S H RX RY hs hr).postcomp L)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputComparisonIso Q S H RX' RY' hs hr') := by
  cases hx
  cases hy
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputComparisonIso_postcomp_heq Q S H RX RY hs hr L
end SerrePositivity.InfinityCategories.Project.DerivedCategories
