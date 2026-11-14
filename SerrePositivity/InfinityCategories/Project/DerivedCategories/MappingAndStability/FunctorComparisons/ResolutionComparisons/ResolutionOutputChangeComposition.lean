module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.ResolutionComparisonPrecompIdentity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.ResolutionComparisons.ResolutionOutputComparisonComposition
/-!
概要：元の指定分解変更比較を、同じ実二経路の前合成比較と入力変換へ同定する。
方針：恒等入力と二段前合成則を保ち、元の指定射の共役式を回収する。
規約：同値の逆と比較を選び直さない。使われ方：元の導来射作用との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
lemma qCatResolutionOutputPrecompIso_comp_left_id
    {X Y Z A B V : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    [Quasicategory A] [Quasicategory B] [Quasicategory V]
    (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X A) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y A) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Z B)
    (k : A ⟶ B) (H : X ⟶ Y) (J : Y ⟶ Z)
    (RX : X ⟶ V) (RY : Y ⟶ V) (RZ : Z ⟶ V)
    (hs : H ≫ S.hom = Q.hom) (ht : J ≫ T.hom = S.hom ≫ k)
    (hu : (H ≫ J) ≫ T.hom = Q.hom ≫ k)
    (hr : H ≫ RY = RX) (hj : J ≫ RZ = RY) (huR : (H ≫ J) ≫ RZ = RX) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso Q T k (H ≫ J) RX RZ hu huR =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputComparisonIso Q S H RX RY hs hr ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso S T k J RY RZ ht hj := by
  have hs' : H ≫ S.hom = Q.hom ≫ 𝟙 A := by
    simpa only [Category.comp_id] using hs
  have hu' : (H ≫ J) ≫ T.hom = Q.hom ≫ (𝟙 A ≫ k) := by
    simpa only [Category.id_comp] using hu
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso_comp Q S T (𝟙 A) k H J RX RY RZ
    hs' ht hu' hr hj huR
  have hi : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputComparisonIso Q S H RX RY hs hr =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso Q S (𝟙 A) H RX RY hs' hr :=
    eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputComparisonIso_precomp_id_heq Q S H RX RY hs hr)
  have hc' : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso Q T k (H ≫ J) RX RZ hu huR =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso Q S (𝟙 A) H RX RY hs' hr ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso S T k J RY RZ ht hj := by
    simpa only [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_id] using! hc
  exact hc'.trans (congrArg (fun e => e ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionOutputPrecompIso S T k J RY RZ ht hj) hi.symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
