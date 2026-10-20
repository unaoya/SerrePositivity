module
public import SerrePositivity.InfinityCategories.Derived.WeakRoofDescentFamilyEvaluation
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
/-- 屋根表示の実輸送を保ち、全選択空間上の作用族を指定評価族に比較する。 -/
def weakRoofDescentTransportEvaluationIso {R Q E Z H K : SSet.{u}} [KanComplex Z]
    (w : R ⟶ Q) (i : Z ⟶ E) (t : R ⟶ E) (j : H ⟶ Q)
    (a₀ a : K ⟶ R) (b : K ⟶ H) (c : K ⟶ Z)
    (T : SSet.Homotopy a₀ a)
    (HQ : SSet.Homotopy (a ≫ w) (b ≫ j)) (HE : SSet.Homotopy (a₀ ≫ t) (c ≫ i)) :
    FunctorIso (weakRoofDescentAction w i t j ≫ (pre b).app Z)
      (SSet.const (functorVertex c)) := by
  have hQ := FunctorIso.precomp (kanPrecompositionHomotopyIso (Z := Z) HQ)
    (weakRoofDescentExtension w i t)
  have hT := FunctorIso.precomp
    (kanPrecompositionHomotopyIso (Z := Z) (functorHomotopyPostcomp T w))
    (weakRoofDescentExtension w i t)
  have hD := FunctorIso.postcomp (weakRoofDescentExtensionIso w i t) ((pre a₀).app Z)
  have hE := FunctorIso.precomp (kanPrecompositionHomotopyIso (Z := Z) HE)
    (weakRoofDescentEvaluation w i t)
  have hI := FunctorIso.postcomp (weakRoofDescentEvaluationIso w i t) ((pre c).app Z)
  have hc : SSet.const (X := weakRoofDescentSpace w i t) (functorVertex (𝟙 Z)) ≫
      (pre c).app Z = SSet.const (functorVertex c) := by
    rw [SSet.const_comp]
    change SSet.const (functorVertex (c ≫ 𝟙 Z)) = _
    rw [Category.comp_id]
  rw [hc] at hI
  simp only [Category.assoc, roofPrecomposition_comp] at hD hI
  simpa only [weakRoofDescentAction, Category.assoc, roofPrecomposition_comp] using
    hQ.symm ≪≫ hT.symm ≪≫ hD ≪≫ hE ≪≫ hI
end SerrePositivity.InfinityCategories
