module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition
/-!
概要：同じ入力を表す二つの分解の実比較から、実出力関手の全関手同型を得る。
方針：同値な入力射影への後合成で同型を回収し、同じ出力射影へ後合成する。
規約：指定した比較射と両方の指定逆を保持する。使われ方：実出力分解の変更比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
variable {E F B T : SSet.{u}} [Quasicategory E] [Quasicategory F]
  [Quasicategory B] [Quasicategory T]
/-- 入力・出力射影を保つ実分解比較が与える、指定逆からの出力全関手同型。 -/
def qCatResolutionOutputComparisonIso (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence E B) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence F B)
    (H : E ⟶ F) (RF : E ⟶ T) (RG : F ⟶ T)
    (hs : H ≫ S.hom = Q.hom) (hr : H ≫ RG = RF) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (Q.inv ≫ RF) (S.inv ≫ RG) := by
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((Q.inv ≫ H) ≫ S.hom) (S.inv ≫ S.hom) := by
    rw [Category.assoc, hs]
    exact Q.invHomIso ≪≫ S.invHomIso.symm
  have d := S.isQCatEquivalence.isFullyFaithful.preimageFunctorIso e
  simpa only [Category.assoc, hr] using d.postcomp RG
end SerrePositivity.InfinityCategories.Project.DerivedCategories
