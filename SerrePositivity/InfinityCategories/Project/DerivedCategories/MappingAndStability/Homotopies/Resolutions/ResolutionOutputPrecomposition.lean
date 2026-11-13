module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition
/-!
概要：異なる入力を持つ二つの実分解比較から、同じ指定逆による出力比較を得る。
方針：同じ全 Hom・実二射影・比較 cochain の等式を保持して構成する。
規約：元の出力の射影性と入力の小ささは不要。使われ方：二変数 Hom の固定入力制限の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
variable {X Y A B T : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  [Quasicategory A] [Quasicategory B] [Quasicategory T]
/-- 両入力射影の指定逆から、同じ実入力前合成に沿う出力比較を回収する。 -/
def qCatResolutionOutputPrecompIso (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X A) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y B)
    (h : A ⟶ B) (H : X ⟶ Y) (RX : X ⟶ T) (RY : Y ⟶ T)
    (hs : H ≫ S.hom = Q.hom ≫ h) (hr : H ≫ RY = RX) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (Q.inv ≫ RX) (h ≫ S.inv ≫ RY) := by
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((Q.inv ≫ H) ≫ S.hom) ((h ≫ S.inv) ≫ S.hom) := by
    rw [Category.assoc, hs]
    have e1 := Q.invHomIso.postcomp h
    have e2 := S.invHomIso.precomp h
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using! e1 ≪≫ e2.symm
  have d := S.isQCatEquivalence.isFullyFaithful.preimageFunctorIso e
  simpa only [Category.assoc, hr] using! d.postcomp RY
end SerrePositivity.InfinityCategories.Project.DerivedCategories
