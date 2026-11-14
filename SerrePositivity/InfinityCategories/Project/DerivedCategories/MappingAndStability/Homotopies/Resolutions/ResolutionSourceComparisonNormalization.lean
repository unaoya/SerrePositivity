module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.ResolutionSourceComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.ResolutionCounitComparison
/-!
概要：元の指定入力・出力比較を、同じ余単位比較へ型付きで正規化する。
方針：端点の等式輸送だけを除き、既存の指定余単位と完全充満性による回収を保持する。
規約：比較同型を選び直さない。使われ方：分解前合成の cocycle 則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
variable {X Y A B : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  [Quasicategory A] [Quasicategory B]
/-- 元の基底比較の指定値は、同じ二つの余単位の比較に型付きで一致する。 -/
lemma qCatResolutionBaseComparisonIso_heq
    (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X A) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y B)
    (h : A ⟶ B) (H : X ⟶ Y) (hs : H ≫ S.hom = Q.hom ≫ h) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionBaseComparisonIso Q S h H hs)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolutionCounitComparison Q.invHomIso S.invHomIso h) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionBaseComparisonIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolutionCounitComparison,
    Eq.mp, Eq.mpr, eqRec_heq_iff]
  rfl
/-- 元の出力比較は、回収した同じ入力比較の出力射影による後合成そのもの。 -/
lemma qCatResolutionOutputPrecompIso_sourceComparison_heq
    {T : SSet.{u}} [Quasicategory T]
    (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X A) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y B)
    (h : A ⟶ B) (H : X ⟶ Y) (RX : X ⟶ T) (RY : Y ⟶ T)
    (hs : H ≫ S.hom = Q.hom ≫ h) (hr : H ≫ RY = RX) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso Q S h H RX RY hs hr)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionSourceComparisonIso Q S h H hs).postcomp RY) := by
  subst RX
  rfl
/-- 入力写像の二表示が等しければ、元の指定出力比較は型付きで同じ値を保つ。 -/
lemma qCatResolutionOutputPrecompIso_heq_of_maps
    {T : SSet.{u}} [Quasicategory T]
    (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X A) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y B)
    {h h' : A ⟶ B} {H H' : X ⟶ Y} (RX : X ⟶ T) (RY : Y ⟶ T)
    (hh : h = h') (hH : H = H')
    (hs : H ≫ S.hom = Q.hom ≫ h) (hr : H ≫ RY = RX)
    (hs' : H' ≫ S.hom = Q.hom ≫ h') (hr' : H' ≫ RY = RX) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso Q S h H RX RY hs hr)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso Q S h' H' RX RY hs' hr') := by
  subst h' H'
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
