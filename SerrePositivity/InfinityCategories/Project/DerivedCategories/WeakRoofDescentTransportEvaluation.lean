module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.WeakRoofDescentFamilyEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
/-!
概要：実屋根表示の輸送を含めて、全降下選択空間上で指定評価族と比較する。
方針：商屋根側の二つの実ホモトピーを Kan 値前合成の関手同型として貼る。
規約：屋根内で輸送の逆ホモトピーを選ばない。使われ方：有限同時細分の評価族。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
/-- 屋根表示の実輸送を保ち、全選択空間上の作用族を指定評価族に比較する。 -/
def weakRoofDescentTransportEvaluationIso {R Q E Z H K : SSet.{u}} [KanComplex Z]
    (w : R ⟶ Q) (i : Z ⟶ E) (t : R ⟶ E) (j : H ⟶ Q)
    (a₀ a : K ⟶ R) (b : K ⟶ H) (c : K ⟶ Z)
    (T : SSet.Homotopy a₀ a)
    (HQ : SSet.Homotopy (a ≫ w) (b ≫ j)) (HE : SSet.Homotopy (a₀ ≫ t) (c ≫ i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentAction w i t j ≫ (pre b).app Z)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c)) := by
  have hQ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kanPrecompositionHomotopyIso (Z := Z) HQ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentExtension w i t)
  have hT := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kanPrecompositionHomotopyIso (Z := Z) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp T w))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentExtension w i t)
  have hD := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentExtensionIso w i t) ((pre a₀).app Z)
  have hE := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kanPrecompositionHomotopyIso (Z := Z) HE)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentEvaluation w i t)
  have hI := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentEvaluationIso w i t) ((pre c).app Z)
  have hc : SSet.const (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentSpace w i t) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 Z)) ≫
      (pre c).app Z = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c) := by
    rw [SSet.const_comp]
    change SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (c ≫ 𝟙 Z)) = _
    rw [Category.comp_id]
  rw [hc] at hI
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPrecomposition_comp] at hD hI
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentAction, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPrecomposition_comp] using
    hQ.symm ≪≫ hT.symm ≪≫ hD ≪≫ hE ≪≫ hI
end SerrePositivity.InfinityCategories.Project.DerivedCategories
