module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.WeakRoofDescentRestriction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.KanEvaluationEdgeIso
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-! # 実屋根の評価辺による全高次降下作用の比較

概要：商側・標的側の実比較辺から、降下空間全体上の作用の値を固定評価値と比較する。
方針：実辺に沿う評価の二胞体を、降下の普遍比較と恒等評価の普遍比較でつなぐ。
規約：各選択点でホモトピーを選び直さない。使われ方：実屋根評価と商 Hom 作用族の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 二つの実屋根比較辺は、降下作用の値と固定評価値を全選択空間上で比較する。 -/
def weakRoofDescentActionEvaluationIso {R Q E Z H : SSet.{u}} [KanComplex Z]
    (w : R ⟶ Q) (i : Z ⟶ E) (t : R ⟶ E) (j : H ⟶ Q)
    (a : R _⦋0⦌) (b : H _⦋0⦌) (c : Z _⦋0⦌)
    (eQ : Truncated.Edge (X := (truncation 2).obj Q)
      (w.app (Opposite.op ⦋0⦌) a) (j.app (Opposite.op ⦋0⦌) b))
    (eE : Truncated.Edge (X := (truncation 2).obj E)
      (t.app (Opposite.op ⦋0⦌) a) (i.app (Opposite.op ⦋0⦌) c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentAction w i t j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b) (SSet.const c) := by
  have hQ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kanEvaluationEdgeIso (Z := Z) eQ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentExtension w i t)
  have hD := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentExtensionIso w i t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Z) a)
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.evaluateFunctorAt_precomp] at hD
  have hE := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kanEvaluationEdgeIso (Z := Z) eE)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentEvaluation w i t)
  have hI := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentEvaluationIso w i t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Z) c)
  have hc : SSet.const (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentSpace w i t) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 Z)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt c = SSet.const c := by
    rw [SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
    rfl
  rw [hc] at hI
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.evaluateFunctorAt_precomp] at hI
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentAction, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.evaluateFunctorAt_precomp] using
    hQ.symm ≪≫ hD ≪≫ hE ≪≫ hI

end SerrePositivity.InfinityCategories.Project.DerivedCategories
